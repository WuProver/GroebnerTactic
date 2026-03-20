# This a python script that connects to a SageMathCell server via WebSocket,
# sends code for execution, and retrieves the results.
import sys
import json
import requests
import websocket
from uuid import uuid4

class SageCell(object):
    def __init__(self, url, timeout=10):
        if not url.endswith('/'):
            url += '/'

        # 1. Request a kernel
        response = requests.post(
            url + 'kernel',
            data={'accepted_tos': 'true'},
            headers={'Accept': 'application/json'}
        ).json()

        self.kernel_url = '{ws_url}kernel/{id}/'.format(**response)

        # 2. Connect to the kernel via WebSocket
        websocket.setdefaulttimeout(timeout)
        self._ws = websocket.create_connection(
            self.kernel_url + 'channels',
            header={'Jupyter-Kernel-ID': response['id']}
        )
        self.shell_messages = []
        self.iopub_messages = []

    def execute_request(self, code):
        self.shell_messages = []
        self.iopub_messages = []
        msg = self._make_execute_request(code)
        self._ws.send(msg)

        got_execute_reply = False
        got_idle_status = False

        while not (got_execute_reply and got_idle_status):
            raw_msg = self._ws.recv()
            msg = json.loads(raw_msg)

            if msg['channel'] == 'shell':
                self.shell_messages.append(msg)
                if msg['header']['msg_type'] == 'execute_reply':
                    got_execute_reply = True
            elif msg['channel'] == 'iopub':
                self.iopub_messages.append(msg)
                if (msg['header']['msg_type'] == 'status' and
                    msg['content']['execution_state'] == 'idle'):
                        got_idle_status = True

        return {'shell': self.shell_messages, 'iopub': self.iopub_messages}

    def _make_execute_request(self, code):
        session = str(uuid4())
        execute_request = {
            'channel': 'shell',
            'header': {
                'msg_type': 'execute_request',
                'msg_id': str(uuid4()),
                'username': '',
                'session': session,
            },
            'parent_header':{},
            'metadata': {},
            'content': {
                'code': code,
                'silent': False,
                'user_expressions': {
                    '_sagecell_files': 'sys._sage_.new_files()',
                },
                'allow_stdin': False,
            }
        }
        return json.dumps(execute_request)

    def close(self):
        self._ws.close()

def extract_result(messages):
    outputs = []
    for msg in messages.get('iopub', []):
        msg_type = msg['header']['msg_type']
        content = msg.get('content', {})

        if msg_type == 'stream' and content.get('name') == 'stdout':
            outputs.append(content.get('text', ''))
        elif msg_type == 'execute_result':
            outputs.append(content.get('data', {}).get('text/plain', ''))
        elif msg_type == 'error':
            outputs.append("\n".join(content.get('traceback', [])))

    return "".join(outputs).strip()


if __name__ == "__main__":
    # sys.argv[1] is the sage code
    # sys.argv[2:] are the logical arguments passed to the sage code
    if len(sys.argv) < 2:
        print("Error: No SageMath code provided.", file=sys.stderr)
        sys.exit(1)

    sage_code = sys.argv[1]
    script_args = sys.argv[2:]

    argv_repr = repr(['sage_script.py'] + script_args)
    injected_code = f"import sys\nsys.argv = {argv_repr}\n\n" + sage_code

    url = 'https://sagecell.sagemath.org'

    try:
        cell = SageCell(url)
        raw_messages = cell.execute_request(injected_code)
        cell.close()

        result = extract_result(raw_messages)
        if result:
            print(result)

    except Exception as e:
        print(f"Error executing request: {e}", file=sys.stderr)
        sys.exit(1)