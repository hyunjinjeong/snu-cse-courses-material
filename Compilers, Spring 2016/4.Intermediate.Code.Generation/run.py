import subprocess
import os
import glob
import difflib
import sys

def hilite(string, color):
  attr = []
  if color == 'green':
    attr.append('32')
  elif color == 'red':
    attr.append('31')
  return '\x1b[%sm%s\x1b[0m' % (';'.join(attr), string)

def main():

  total = 0
  success = 0

  testdir = None
  if(len(sys.argv) == 2 and not sys.argv[1].endswith(".mod")):
    testdir = sys.argv[1]

    for root, dirs, files in os.walk(testdir):
      for f in files:
        if f.endswith(".mod"):
          total += 1
          f = os.path.join(root, f)
          with open("ref", "w") as refout, open("you", "w") as youout:
            #print("running", f)
            #print("diff reference and yours")

            ref = subprocess.Popen(["./reference/4_test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            refout.write(ref.stdout.read().decode())
            refout.write(ref.stderr.read().decode())

            yours = subprocess.Popen(["./snuplc/test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            youout.write(yours.stdout.read().decode())
            youout.write(yours.stderr.read().decode())

          with open("ref", "r") as refin, open("you", "r") as youin:
            reflines = refin.readlines()
            youlines = youin.readlines()
            for i in range(len(reflines)):
              reflines[i] = reflines[i].replace('tRBrak', 'tRSBrak')
              reflines[i] = reflines[i].replace('tVarDecl', 'tVar')

            d = difflib.Differ()
            diff = d.compare(reflines, youlines)
            cnt = 0
            for line in diff:
              if line[0] == '-':
                if sys.stdout.isatty():
                  print(hilite(line, 'red'), end='')
                else:
                  print(line, end='')
                cnt += 1
              elif line[0] == '+':
                if sys.stdout.isatty():
                  print(hilite(line, 'green'), end='')
                else:
                  print(line, end='')
                cnt += 1

          if cnt == 0:
            success += 1
            #print("all same")
          else:
            print("above differences at file : ", f)

          subprocess.Popen(["rm", "ref"]).communicate()
          subprocess.Popen(["rm", "you"]).communicate()

  elif(len(sys.argv) == 2 and sys.argv[1].endswith(".mod")):
    f = sys.argv[1]
    total += 1
    #f = os.path.join(root, f)
    with open("ref", "w") as refout, open("you", "w") as youout:
      #print("running", f)
      #print("diff reference and yours")

      ref = subprocess.Popen(["./reference/4_test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      refout.write(ref.stdout.read().decode())
      refout.write(ref.stderr.read().decode())

      yours = subprocess.Popen(["./snuplc/test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      youout.write(yours.stdout.read().decode())
      youout.write(yours.stderr.read().decode())

      with open("ref", "r") as refin, open("you", "r") as youin:
        reflines = refin.readlines()
        youlines = youin.readlines()
        for i in range(len(reflines)):
          reflines[i] = reflines[i].replace('tRBrak', 'tRSBrak')
          reflines[i] = reflines[i].replace('tVarDecl', 'tVar')

        d = difflib.Differ()
        diff = d.compare(reflines, youlines)
        cnt = 0
        for line in diff:
          if line[0] == '-':
            if sys.stdout.isatty():
              print(hilite(line, 'red'), end='')
            else:
              print(line, end='')
            cnt += 1
          elif line[0] == '+':
            if sys.stdout.isatty():
              print(hilite(line, 'green'), end='')
            else:
              print(line, end='')
            cnt += 1

      if cnt == 0:
        success += 1
        #print("all same")
      else:
        print("above differences at file : ", f)

      subprocess.Popen(["rm", "ref"]).communicate()
      subprocess.Popen(["rm", "you"]).communicate()
  else:
    testdir = "./test"

    for root, dirs, files in os.walk(testdir):
      for f in files:
        if f.endswith(".mod"):
          total += 1
          f = os.path.join(root, f)
          with open("ref", "w") as refout, open("you", "w") as youout:
            #print("running", f)
            #print("diff reference and yours")

            ref = subprocess.Popen(["./reference/4_test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            refout.write(ref.stdout.read().decode())
            refout.write(ref.stderr.read().decode())

            yours = subprocess.Popen(["./snuplc/test_ir", f], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            youout.write(yours.stdout.read().decode())
            youout.write(yours.stderr.read().decode())

          with open("ref", "r") as refin, open("you", "r") as youin:
            reflines = refin.readlines()
            youlines = youin.readlines()
            for i in range(len(reflines)):
              reflines[i] = reflines[i].replace('tRBrak', 'tRSBrak')
              reflines[i] = reflines[i].replace('tVarDecl', 'tVar')

            d = difflib.Differ()
            diff = d.compare(reflines, youlines)
            cnt = 0
            for line in diff:
              if line[0] == '-':
                if sys.stdout.isatty():
                  print(hilite(line, 'red'), end='')
                else:
                  print(line, end='')
                cnt += 1
              elif line[0] == '+':
                if sys.stdout.isatty():
                  print(hilite(line, 'green'), end='')
                else:
                  print(line, end='')
                cnt += 1

          if cnt == 0:
            success += 1
            #print("all same")
          else:
            print("above differences at file : ", f)

          subprocess.Popen(["rm", "ref"]).communicate()
          subprocess.Popen(["rm", "you"]).communicate()

  print()
  print("score", success, "/", total)


if __name__ == "__main__":
  main()
