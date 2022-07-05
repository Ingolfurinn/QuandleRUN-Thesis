import sys
import re
import distutils.text_file as txt
import os

for x in sys.argv[1:]:
    graphfile = txt.TextFile(x, file=None, strip_comments=True, join_lines=True)
    lines = graphfile.readlines()
    file = open(f'{x[:-4]}.dot', 'w')
    text = ""
    regex_compilation = re.compile(r"<(\d{1,}),\s{0,}(true|false){1},\s{0,}(true|false){1}>")
    file.write("graph { \n nodesep = 0.5; \n  node [ shape = circle, width = 0.1 ]; \n")
    nodes = []

    edges = []

    entire_text = ""
    for line in lines[2:]:
        entire_text += line

    lines = entire_text.split(';')
    for index in range(len(lines)):
        lines[index] += ';'

    for line in lines:
        print(line)
        result = regex_compilation.findall(line)

        if result == []:
            continue
        node = f"node{result[0][0]} [ label=\" \", style=\"filled\", "
        if result[0][2] == 'true':
            nodes.append(node + "fillcolor=gold ] \n")
        elif result[0][1] == 'true':
            nodes.append(node + "fillcolor=olivedrab1 ] \n")
        else:
            nodes.append(node + "fillcolor=none ] \n")

        for index in range(1, len(result), 1):
            edges.append(f"node{result[index][0]} -- node{result[0][0]}\n")

    print(edges)
    print(nodes)
    #
    for node in nodes:
        file.write(node)
    file.write("\n")
    for edge in edges:
        file.write(edge)
    #
    file.write("}")
    file.close()
    os.system(f"dot -Teps {x[:-4]}.dot -o {x[:-4]}.eps")
    os.system(f"open {x[:-4]}.eps")

