## cnfgen-nand-opt

This program can generate CNF (Conjunctive Normal Form) to check possibility to build
circuit built on NAND or NOR gates that returns given values from table.
This program can read problem from file. If no given file then program read problem
from standard input. The format of input is in TOML format:

```
gate = "Nand"
layers = 5
max_gates = 18
table = [ 6, 62, 11, 17, 26, 47, 53, 35 ]
```

The `gate` field is gate type - it can be `Nand` or `Nor`. The `layers` defines number
of layers (steps) of calcuation in circuit. The `max_gates` defines maximal number of
gates. The `table` is table of values that should be returned by circuit.

List of commands:

* generate - Generate CNF file and print it to standard output.
* execute - Generate CNF file and pass it to SAT solver, check and print results. SAT_SOLVER environment variable must be set to path to SAT solver executable.
* check - Check and print results from SAT output. The SAT output file given as the second argument after command or the first FILE is not given.
* help - Print help.
