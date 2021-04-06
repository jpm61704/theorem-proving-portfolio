# theorem-proving-portfolio

Hello Favonia, Jonathan, Carlo, Matthew and Friends!

I've included in this repo a variety of projects and practice files that I've produced over the last few years while getting experience with theorem provers. Below is a synopsis and explanation of each of the folders. As far as I'm aware, all of the projects use an older version of the Agda standard library. However, I believe it should still work with the newer versions. Please let me know if this is not the case and I can update the imports to work properly. 

Thanks for opportunity! I'm looking forward to hearing back!

Jack Martin

## Projects (oldest-to-newest)
This is a brief overview of some of the projects and tutorials I've worked. The two main folders from PLFA and Fundamentals of Programming Languages are included above. I would point you primarily to some of the later homeworks in the FPL folder along with the term project to see some of the larger proofs I've written.

* **Software Foundations (Coq)** <br /> Initial exposure to Coq and theorem proving in a graduate-level Formal Methods course I completed during my undergraduate studies at the University of Missouri under Rohit Chadha.
* **Programming Language Foundations in Agda** <br/> Completion of Parts I & II of Wadler, Kokke, & Siek's PLFA book. This was my primary tutorial and introduction into Theorem Proving. I've completed most of the modules a few times on a few machines so many of the files are lost to the Ether. I've included as much as I could find though!
* **Mechanization of Fundamentals of Programming Languages** (Graduate PL class at CU Boulder) <br/> I decided, along with my advisor Evan Chang, to add an additional challenge to the graduate-level programming languages course by implementing all of the homework in Agda(with proofs) instead of in OCaml. Much of this was very similiar to Part 2 of PLFA, but there is also quite a bit that is different, including the implementation and proofs for a stack machine executing the lambda calculus. 
* **Typing Universes for Program Search** <br /> As my term project for the graduate course in PL, I implemented a basic embedded-search tool to find declarations matching a given type in Agda, using a type universe such that the definitions and search functionality can live in the same file. The goal of this work was to expand its use for applications in program synthesis, this work will hopefully still be done at some point in the future. 
* **Proof Reuse under transformation** <br /> This, unfinished, work was a dive into the question "what happens to proofs terms when the term they describe is altered by a transformation, what need's to be recomputed?". The primary example is that of changing the root of a binary search tree. The entire proof tree of the BST need not be thrown out, but rather only the altered nodes need to be updated, so long as the tree is still a BST. This is just a short description, but please feel free to ask more about the project! The code isn't included here as it is largely underdocumented and far from finished.
