"""Consistent, non-overwriting JSON output for the public command-line tools."""
import json


def prepare_output(parser, output):
    """Reject existing names, including dangling symlinks, before computation.

    This is a usability preflight, not the race-safety mechanism. The final
    write still uses exclusive creation. No file is reserved or created here.
    """
    if output is None:
        return
    try:
        output.lstat()
    except FileNotFoundError:
        return
    except OSError as error:
        parser.exit(2, f'output error: cannot inspect {output}: {error}\n')
    parser.exit(2, f'output error: {output} already exists; choose a new path\n')


def emit_json(parser, result, output):
    """Print JSON, optionally exclusively creating a new output file.

    Call only after computation has succeeded: failed computations then leave
    no output file. Mode 'x' rejects a target created after the preflight and
    never follows an existing final-component symlink.
    """
    payload = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if output is not None:
        try:
            with output.open('x', encoding='utf-8') as stream:
                stream.write(payload)
        except FileExistsError:
            parser.exit(2, f'output error: {output} already exists; choose a new path\n')
        except OSError as error:
            parser.exit(2, f'output error: cannot create {output}: {error}\n')
    print(payload, end='')
