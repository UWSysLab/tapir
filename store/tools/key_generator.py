import random
import string
import sys

charset = string.ascii_uppercase + string.ascii_lowercase + string.digits

for i in range(int(sys.argv[1])):
  rkey = "".join(random.choice(charset) for j in range(64))
  print rkey
