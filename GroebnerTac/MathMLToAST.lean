import GroebnerTac.AST

private inductive XMLNode where
  | element (tag : String) (children : List XMLNode)
  | text (content : String)
  | selfClosing (tag : String)

private partial def parseXMLElement (s : String) : Option (String × String × String) :=
  if !s.startsWith "<" then none
  else
    let s' := s.drop 1
    match s'.splitOn ">" with
    | tagPart :: rest =>
      let cleanTag := if tagPart.endsWith "/" then tagPart.dropRight 1 else tagPart
      let content := String.intercalate ">" rest
      let closeTag := s!"</{cleanTag}>"

      -- Find the MATCHING closing tag by counting nesting
      let rec findMatchingClose (remaining : String) (depth : Nat) (pos : Nat) : Option (Nat × String) :=
        if pos >= remaining.length then none
        else if remaining.drop pos |>.startsWith s!"<{cleanTag}>" then
          findMatchingClose remaining (depth + 1) (pos + cleanTag.length + 1)
        else if remaining.drop pos |>.startsWith closeTag then
          if depth == 0 then
            some (pos, remaining.drop (pos + closeTag.length))
          else
            findMatchingClose remaining (depth - 1) (pos + closeTag.length)
        else
          findMatchingClose remaining depth (pos + 1)

      match findMatchingClose content 0 0 with
      | some (endPos, remaining) =>
        let inner := content.take endPos
        some (cleanTag, inner, remaining)
      | none => some (cleanTag, content, "")
    | [] => none

private partial def parseXML (s : String) : List XMLNode :=
  let s := s.trim
  if s.isEmpty then []
  else if s.startsWith "<" then
    if s.startsWith "</" then
      let afterClosingTag := s.dropWhile (· != '>') |>.drop 1
      parseXML afterClosingTag
    else
      let firstTagEnd := s.takeWhile (· != '>')
      if firstTagEnd.endsWith "/" then
        let tagName := firstTagEnd.drop 1 |>.dropRight 1
        let remaining := s.dropWhile (· != '>') |>.drop 1
        XMLNode.selfClosing tagName :: parseXML remaining
      else
        match parseXMLElement s with
        | some (tag, inner, remaining) =>
          let children := parseXML inner
          XMLNode.element tag children :: parseXML remaining
        | none => [XMLNode.text s]
  else
    let nextTagPos := s.toList.findIdx? (· == '<')
    match nextTagPos with
    | none => [XMLNode.text s]
    | some pos =>
      if pos == 0 then parseXML s
      else
        let textPart := s.take pos
        let remaining := s.drop pos
        if textPart.trim.isEmpty then
          parseXML remaining
        else
          XMLNode.text textPart :: parseXML remaining

private def stringContains (s : String) (substr : String) : Bool :=
  (s.splitOn substr).length > 1

private def getLastAfterColon (s : String) : String :=
  match s.splitOn ":" with
  | [] => s
  | parts => parts.getLast!

private partial def xmlToAST (node : XMLNode) : Option MathAST :=
  match node with
  | XMLNode.text content =>
    if content.trim.isEmpty then none  -- Filter out empty text
    else parseLeaf content.trim
  | XMLNode.selfClosing tag =>
    if tag.trim.isEmpty then none  -- Filter out empty tags
    else
      let result := some (MathAST.string tag)
      result
  | XMLNode.element tag children =>
    if tag.trim.isEmpty then none  -- Filter out empty tags
    else
      let childASTs := children.filterMap xmlToAST
      match tag with
      | "math" | "mrow" | "item" =>
        match childASTs with
        | [single] =>
          some single
        | _ =>
          some (MathAST.list childASTs)

      -- Content MathML
      | "eq" | "plus" | "minus" | "times" | "divide" | "power" | "root" =>
        some (MathAST.string tag)
      | "apply" =>
        let (operators, operands) := childASTs.partition (fun ast =>
          match ast with
          | MathAST.string op => op ∈ ["eq", "plus", "minus", "times", "divide", "power", "root", "cos", "sin", "tan", "exp", "log", "ln", "si", "int"]
          | _ => false)
        match operators with
        | [MathAST.string op] =>
          let result := some (applyOperator op operands)
          result
        | _ =>
          none
      | "msqrt" =>
        match childASTs with
        | [arg] => some (MathAST.func "sqrt" [arg])
        | _ => none
      | "list" => some (MathAST.list childASTs)
      | "bvar" =>
        match childASTs with
        | [var] => some var
        | _ => none
      | "lowlimit" =>
        match childASTs with
        | [limit] => some limit
        | _ => none
      | "uplimit" =>
        match childASTs with
        | [limit] => some limit
        | _ => none
      | _ =>
        if stringContains tag ":" then
          let cleanTag := getLastAfterColon tag
          match cleanTag with
          | "mi" => some (MathAST.var (getTextContent children) "Real")
          | "mn" => parseLeaf (getTextContent children)
          | "mo" => some (MathAST.string (getTextContent children))
          | "msub" =>
            -- Handle subscripted variables like t_0 -> "t0"
            match childASTs with
            | [MathAST.var base _, MathAST.nat idx] => some (MathAST.var s!"{base}{idx}" "Real")
            | [MathAST.var base _, MathAST.var idx _] => some (MathAST.var s!"{base}_{idx}" "Real")
            | _ => some (MathAST.list childASTs)
          | _ =>
            if childASTs.length == 1 then childASTs.head?
            else if childASTs.isEmpty then none
            else some (MathAST.list childASTs)
        else
          dbg_trace s!"Unknown tag '{tag}' with {childASTs.length} children"
          if childASTs.length == 1 then childASTs.head?
          else if childASTs.isEmpty then none
          else some (MathAST.list childASTs)

where
  parseLeaf (s : String) : Option MathAST :=
    if s == "True" then some (MathAST.bool true)
    else if s == "False" then some (MathAST.bool false)
    else if let some n := s.toNat? then some (MathAST.nat n)
    else if let some i := s.toInt? then some (MathAST.int i)
    else if s.length == 1 && s.all Char.isAlpha then some (MathAST.var s "Real")
    else some (MathAST.string s)

  getTextContent (nodes : List XMLNode) : String :=
    String.join (nodes.map fun node =>
      match node with
      | XMLNode.text s => s.trim
      | XMLNode.element tag children =>
        if stringContains tag ":" then
          let cleanTag := getLastAfterColon tag
          match cleanTag with
          | "mi" | "mn" => getTextContent children
          | "msub" =>
            -- Convert t_0 to "t0"
            match children with
            | [baseNode, idxNode] =>
              let base := getTextContent [baseNode]
              let idx := getTextContent [idxNode]
              s!"{base}{idx}"
            | _ => ""
          | _ => ""
        else ""
      | _ => "")

  applyOperator (op : String) (operands : List MathAST) : MathAST :=
    match op, operands with
    | "eq", [a, b] => MathAST.eq a b
    | "plus", [] => MathAST.nat 0
    | "plus", [x] => x
    | "plus", args => MathAST.add args
    | "times", [] => MathAST.nat 1
    | "times", [x] => x
    | "times", args =>
      let hasVar := args.any (fun ast => match ast with | MathAST.var _ _ => true | _ => false)
      if hasVar then MathAST.mul args else MathAST.mul args
    | "minus", [x] => MathAST.neg x
    | "minus", [x, y] => MathAST.sub x y
    | "minus", args =>
      -- Handle multiple operands: a - b - c = a - (b + c)
      match args with
      | [] => MathAST.nat 0
      | [x] => MathAST.neg x
      | x :: rest => MathAST.sub x (MathAST.add rest)
    | "divide", [x] => MathAST.div x (MathAST.nat 1)
    | "divide", [x, y] => MathAST.div x y
    | "power", [x, y] => MathAST.pow x y
    | "root", [x] => MathAST.func "sqrt" [x]
    | "cos", [x] => MathAST.func "cos" [x]
    | "sin", [x] => MathAST.func "sin" [x]
    | "tan", [x] => MathAST.func "tan" [x]
    | "exp", [x] => MathAST.func "exp" [x]
    | "log", [x] => MathAST.func "log" [x]
    | "ln", [x] => MathAST.func "ln" [x]
    | _, _ =>
      dbg_trace s!"Unknown operator '{op}' with {operands.length} operands: {repr operands}"
      MathAST.string "error"

-- Main entry point
partial def mathMLToAST (input : String) : Option MathAST :=
  let nodes := parseXML input
  match nodes with
  | [single] => xmlToAST single
  | multiple => some (MathAST.list (multiple.filterMap xmlToAST))
