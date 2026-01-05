#!/usr/bin/env python

from popper.util import Settings
from popper.loop import learn_solution

if __name__ == '__main__':
    settings = Settings(cmd_line=True)
    import logging
    l = logging.getLogger("popper.termination")
    l.addHandler(logging.StreamHandler())
    l.setLevel(logging.DEBUG)
    l = logging.getLogger("popper.loop")
    l.addHandler(logging.StreamHandler())
    l.setLevel(logging.DEBUG)
    prog, score, stats = learn_solution(settings)
    if prog is not None:
        settings.print_prog_score(prog, score)
    else:
        print('NO SOLUTION')
    if settings.show_stats:
        stats.show()
