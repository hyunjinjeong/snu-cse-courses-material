import subprocess
import os
import glob
import difflib
import sys
from modgen import *

def hilite(string, color):
  attr = []
  if color == 'green':
    attr.append('32')
  elif color == 'red':
    attr.append('31')
  return '\x1b[%sm%s\x1b[0m' % (';'.join(attr), string)

def main():

  if len(sys.argv) < 2:
    print('usage : python3 snuplc_test.py reference yours [save_wrongfiles_at="wrongfiles"] [funcnum=5] [statnum=10] [statlength=100]')
    exit()

  reference_program = sys.argv[1]
  your_program = sys.argv[2]

  savewrongfiles = "wrongfiles"
  if len(sys.argv) >= 4:
    savewrongfiles = sys.argv[3]
  funcnum = 3
  if len(sys.argv) >= 5:
    funcnum = int(sys.argv[4])
  statnum = 3
  if len(sys.argv) >= 6:
    funcnum = int(sys.argv[5])
  statlength = 3
  if len(sys.argv) >= 7:
    statlength = int(sys.argv[6])

  if not os.path.exists(savewrongfiles):
    os.makedirs(savewrongfiles)
  tempdir = "__temp__"
  if not os.path.exists(tempdir):
    os.makedirs(tempdir)

  total = 0
  success = 0
  wrongcount = 0

  tempfilename = os.path.join(tempdir, "temp.mod")
  reffilename = os.path.join(tempdir, "ref.temp.mod.s")
  yoursfilename = os.path.join(tempdir, "yours.temp.mod.s")
  res = True

  while res:
    m = Module("test", funcnum, statnum, statlength)
    with open(tempfilename, "w") as modfile:
      print(m, file=modfile)

    subprocess.Popen([reference_program, tempfilename], stdout=subprocess.PIPE).communicate()
    subprocess.Popen(["cp", tempfilename + ".s", reffilename]).communicate()

    subprocess.Popen([your_program, tempfilename], stdout=subprocess.PIPE).communicate()
    subprocess.Popen(["cp", tempfilename + ".s", yoursfilename]).communicate()

    with open(reffilename, "r") as refin, open(yoursfilename, "r") as youin:
      reflines = refin.readlines()
      youlines = youin.readlines()

      d = difflib.Differ()
      diff = d.compare(reflines, youlines)

      diffs = []
      for d in diff:
        diffs.append(d)
      diff = diffs

      different = False
      for line in diff:
        if line.startswith('-') or line.startswith('+'):
          different = True
          break

      if different: #different
        subprocess.Popen(["cp", tempfilename, os.path.join(savewrongfiles, "wrong" + str(wrongcount) + ".mod")]).communicate()
        with open(os.path.join(savewrongfiles, "log" + str(wrongcount)), "w") as log:
          for line in diff:
            if line.startswith('-') or line.startswith('+'):
                print(line, end='', file=log)
        wrongcount += 1
        res = False

      else: # success
        success += 1

      total += 1
      print(str(success) + '/' + str(total), end="\r")



if __name__ == "__main__":
  main()
