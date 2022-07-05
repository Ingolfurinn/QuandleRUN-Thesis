# QuandleRUN-Thesis

This is a repository for my Bachelor graduation project and Honours Academy final project. 

## Installation guide for "Software"

* Only QuandleRUN:
  1. Install [Magma](magma.maths.usyd.edu.au).
  2. Place __QuandleRUN__ in the folder where you keep your packages(referred to as ``packages``).
  3. Launch Magma.
  4. Enter ``AttachSpec("packages/QuandleRUN");``.
  5. Enjoy. 

* QuandleRUN + Examples:
  1. Follow the guid above to install Magma. 
  2. Install [Python 3.8.9 (It would probably also work with later releases)]([https://www.python.org](https://www.python.org/downloads/release/python-389/))
  3. Install [graphviz](graphviz.org).
  
 ### Running the examples
 
1. Launch Magma. 
2. Load the example: ``load "examples/EXAMPLE[for example: Subquandles]/FILENAME[for example: SubquandlesExample]``.
3. Quit Magma.
4. Run the converting script: ``ls | grep .txt | xargs -n 1 python3 examples/EXAMPLE[for example: Subquandles]/Convert.py``.
