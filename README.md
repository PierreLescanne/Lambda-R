# -
Lambda calculus with explicit duplication and erasure (in Agda)

In this repository, you will find a project under development, namely the Agda code for a lambda-calculus with explicit duplication and erasure (aka a lambda-calculus with explicit resource control).
Currently there are 9 files:

* LambdaL.agda : a file specifically for a submission to [Formal Aspects of Computing](https://dl.acm.org/journal/fac)
* Examples_for_LambdaL : a set of examples for LambdaL.agda
* -----------------------
* Nat_complement.agda : complements on the naturals
* Lambda.agda : plain lambda calculus
* LIST.agda : a specific implementation of lists, targeted toward sorted lists.
* Lambda_WITH_LIST.agda : the implemenation of linear lambda-calulus.
* Is-lin.agda : a apendix of the previous file (a test on linearity of plain lambda-terms) 
* Sort.agda : applications of LIST to sorting algorithms (insertion sort and merge sort) 
* Examples_for_Lambda_WITH_LIST.agda : some exmaples
* L-types-for-resource-awarness.pdf : a paper presenting the theory (with better presentation of the programs than in the arXiv paper)
