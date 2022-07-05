import sys
import re
import distutils.text_file as txt
import os

for x in sys.argv[1:]:

    graphfile = txt.TextFile(x, file=None, strip_comments=True, join_lines=True)
    lines = graphfile.readlines()
    file = open(f'{x[:-4]}.dot', 'w')
    text = ""
    regex_compilation = re.compile(r"(<\d{1,},\s\d{1,}>)\s{1,}")
    file.write("digraph { \n nodesep = 0.5; \n  node [ shape = circle, width = 0.7 ]; \n edge [ style = invis ]; \n")
    nodes = []
    by_cardinality = {}
    edges = []

    for line in lines[2:]:

        result = regex_compilation.findall(line)
        if result == []:
            continue


        if len(result) > 1:
            ID = re.findall("\d{1,}", result[0])
            try:
                by_cardinality[ID[0]].append(result[0])
            except:
                by_cardinality[ID[0]] = [result[0]]

            for index in range(1, len(result), 1):
                if (result[index] != '<1, 1>') and (result[index] != result[0]):
                    ID2 = re.findall("\d{1,}", result[index])
                    if int(ID[0]) >= int(ID2[0]):
                        edges.append(f"{result[0]} -> {result[index]}\n")

    for key in by_cardinality:
        file.write("{ rank = same; ")
        for element in by_cardinality[key]:
            file.write(f"{element} ")
        file.write("} \n")

    key_list = list(by_cardinality.keys())

    for index in range(len(key_list) - 1):
        file.write(f"{by_cardinality[key_list[index]][0]} -> ")
    file.write(f"{by_cardinality[key_list[len(key_list)-1]][0]}; \n")

    file.write("edge [ style = solid ]; \n")

    for edge in edges:
        file.write(edge)

    file.write("}")
    file.close()
    os.system(f"dot -Teps {x[:-4]}.dot -o {x[:-4]}.eps")
    os.system(f"open {x[:-4]}.eps")


