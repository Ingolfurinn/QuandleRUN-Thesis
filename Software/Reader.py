import distutils.text_file as txt
import json
import sys

# Opens the file containing the database
SmallQuandles = txt.TextFile("SmallQuandlesJSON.json", file=None, strip_comments=True, join_lines=True)

# Reads the entire file: it creates a list where each element is a line of the database.
lines = SmallQuandles.readlines()

text = ""

# It creates a string joining all the lines read above
for line in lines:
    text += line

# It decodes the JSON code and gives a dictionary {"key1": value1, "key2": value2, ...}
data = json.loads(text)

# sys.argv[x] reads the arguments passed by the terminal at position x
# (starting from 0, where sys.argv[0] is the name of the program).
# sys.argv[1] is number c, the cardinality of the underlying set of the Quandle.
# sys.argv[2] is a number n, used to select the n-th Quandle of cardinality c.
# data[c,n] says that we want all the information we have on the n-th Quandle with cardinality c;
# At the moment we only have the matrices.
# data[c,n]["matrix"] means that we want the integral quandle matrix of the n-th Quandle with cardinality c.

try:
    matrix = data[f"{(int(sys.argv[1]), int(sys.argv[2]))}"]["matrix"]
    print(matrix)
except:
    print()
    
