
# LGRIP

## Inductive Theorem Prover

* Inductive Theorem Prover and Lemma Generator based on Rewriting Induction Prover for many-sorted TRSs in MSTRS format

This tool will conjecture lemmas by divergence critic,
lemma generation based on difference match and generalization ,
lemma generation based on generating randomly rhs of lemmas.

The system is tested on SML/NJ v110.77.
You need SML/NJ to be installed on your box. 

You need Yices2.2 to be installed on this directory. 
You need to rename excutable file(yices2.2) to yices.

For non x86-linux systems, invoke the SML/NJ interpreter, 
and run
```
 - CM.make "sources.cm";
 - SMLofNJ.exportFn ("ind", Main.main);
 ```
to compile. Also replace "x86-linux" accordingly to run.

To run the command, 
```
 $ sml @SMLload=ind.x86-linux filename [Option]

[Option]
-D     --debug      : we display proof process.
-d=INT --depth=INT  : when we conjecture lemmas by random generation of rhs of lemmas,
                      we decide how much to make the depth of rhs of lemma.
                      The default is the depth of rhs of lemma.
-nI    --noIteration: when we prove lemmas, we don't use the lemma generation.
```
You can find sample files in the director test/.

