# CSCI 5535 - Fundamentals of Programming Languages

* ***Homework 0*** <br/> The attached problem was a basic refresher on the use of inference rules to define properties over sets. It primarily deals with ordered "unshufflings" of a deck of cards into two new decks. There are notably only four cards, one for each suit, available in the decks, but cards are allowed to be repeated.

* ***Homework 1*** <br/> Expands on Homework 0 with a property describing the deck's size as Even or Odd in the usual way. Induction principles are defined for both Even and Odd. This exercise was used to expose the notion of mutual inductive definition. Included is another property called Cut, which describes cutting a deck in the typical way. This property was used to show that two "cuts" that are even, must have come from an even deck.

* ***Homework 2*** <br/> Is the first of several implementations of a basic lambda calculus. The syntax is given in lang.agda. The language is typed  and includes a simple type checking and inference function. The languages includes types for numbers, strings, non-recursive functions, units, products, and sums. Both big and small step operational semantic rules are given in this file as well. In properties.agda, the proofs for progress and preservation are given, including an interpretation function based on the use of gas to bound the size of the evaluation(mechanism taken from PLFA). Most of this module rehashes the first few chapters of Wadler et al.'s PLFA.

* ***Homework 3*** <br/> Implements, on top of the work from Homework 2, Plotkin's System PCF for recursive functions and the language FPC for recursive types. These are implemented using the inference rules from Bob Harper's "Practical Foundations for Programming Languages". The file structure is the same as for Homework 2.

* ***Homework 4*** <br /> This assignment was concerned with implementing the K stack machine as described in Harper's PFPL chapter on Control Stacks (Ch28 in my copy of the text). 

* ***Term Project*** <br /> Is best described in the pdf included in the folder(project-dependent-search) for the project. At a high level, we created a type universe in Agda that allowed a user to encode a library of Agda code and then search for a term matching a type in that code to fill a hole in a program. Please reach out if the pdf isn't an sufficient explanation and I'd be happy to do a demo!



