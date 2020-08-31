# Puns

coqlude, which so far I just think is funny.
coqney, which Paul at least thinks is funny.
stockcoq, which I think is funny and appropriate
doodledo, for a future monad library
concoqtions, which I think is funny and appropriate
peacoq
gif: dont coq it up
coqnisant
incoqnito
gif: lambda calculus

# Coq Art

The Coq system uses a very expressive variation on a typed calculus, the Calculus of Inductive Constructions 

Chapter 3 of this book covers the relation between proofs and programs, generally called the Curry-Howard isomorphism. 

An important characteristic of the Calculus of Constructions is that every type is also a term and also has a type. The type of a proposition is called Prop. For instance, the proposition 3 :s: 7 is at the same time the type of all proofs that 3 is smaller than 7 and a term of type Prop.

This correspondence between A-calculus as a model of functional program- ming and proof calculi like natural deduction [77] is called the "Curry-Howard isomorphism."

# Five Stages of Accepting Constructive Mathematics

https://www.youtube.com/watch?v=zmhd8clDd_Y

In Classical Mathematics
LEM: forall P in Prop, P \/ not P.
is seen as obvious.

Lots of things are proved by contradiction:
Proof by contradiction: forall P, not not P -> P.

LEM is not used in constructive mathematics.
It might be true for certain cases,
but it is not a given and it has to be proven for these specific cases.

It has to be a decision procedure for LEM to hold.

Every set in constructive mathematics has a hidden structure/encoding.
So not really possible to say two sets of equal, 
except if you redefine equality to be set specific.

Taking away the LEM does not abolish standard mathematics.

Computer Scientists naturally gravitate towards constructive mathematics.

You can get used to the anxiety of not having LEM.

A typical piece of classical mathematics, is mostly constructive anyway.
Have you ever heard a category theorist say:
"I want to prove that this diagram commutes, lets suppose it doesn't"
Have you ever heard a computer scientist say:
"I need an algorithm, lets suppose it is not computable"

Turing's Halting Problem is completely constructive

"""
From a psychological point of view, learning constructive mathematics is agonizing, for it requires one to first unlearn certain deeply ingrained intuitions and
habits acquired during classical mathematical training.
""" - https://www.ams.org/journals/bull/2017-54-03/S0273-0979-2016-01556-4/S0273-0979-2016-01556-4.pdf

# Stackoverflow what-is-dependent-typing

https://stackoverflow.com/questions/9338709/what-is-dependent-typing

```
def min(i : Int, j : Int) : BoundedInt(j) =
  if i < j then i else j
```

# Induction and recursion (natural numbers and trees)

https://www.youtube.com/watch?v=fbt0TcLzrNg

Print Nat_ind.
f_equal tactic.

# A Little Taste of Dependent of Dependent Types - David Christiansen

https://www.youtube.com/watch?v=VxINoKFm-S4

Brouwer: Intiotionism - Truth as Construction
Martin-Lof: Intuitionistic Type Theory
Coquand and Huet: The Calculus of Constructions
Luo: UTT
Coq

# "Propositions as Types" by Philip Wadler

https://www.youtube.com/watch?v=IOiZatlZtGU

Gerhard Gentzen
Natural Deduction
Corresponds to
Typed Lambda Calculus

A \/ B -> B \/ A

False has no sub components
"What part of No do you not understand"

## Curry Howard Isomorphism

Proposition corresponds to types
Proofs corresponds to programs
Normalization or Simplification of proofs corresponds to evaluation of programs.

Curry Howard Isomorphism: + -> x bottom

forall is where dependent types starts.


(A, B) -> (B, A)

A => B
A -> B

A -> B   A
----------
B


Classical-Intuitionistic Embedding
Corresponds to
Continuation Passing Style

"Curry-Howard is a double barreled name,
that predicts there will be other double barreled names.

Every good idea will be discovered twice.
Once by a logician and once by a computer scientist.
"

What does this say about the impact of computer science on knowledge in general? "I work in a school of informatics,
and I think informatics is a much better word to use.
Computer science, there are only two things wrong with it
the word computer and the word science,
because it is not just about the computer,
it is about patterns of information
and you don't put science in your name if you are a real science"

# Vladimir Voevodsky Notes

https://www.youtube.com/watch?v=E9RiR9AcXeE

He earned a Fields Medal

Another author, not Voevodsky
Mistake in Lemma 1.1 a one paragraph proof, found at the top of their paper.
The key lemma on which everything else in the paper depended.
was found years later when trying to create a lecture on the paper
Republished 3 pages proof for Lemma 1.1.
It took years for this proof to be accepted.

Carlos Simpson found a counter example to a proof, 9 years after Voevodsky published a paper.
Voevodsky was so sure his proof was right, he didn't believe it was wrong for another 16 years.
It wasn't just Voevodsky,
even the specialists in the field, thought the proof might be wrong,
but still wasn't confident enough to push the issue.

He was faced with writing 1000 pages of formulas to verify his new idea.
"The areas I found of value and of beauty, I didn't have tools to explore"
The only long term solution, seemed to be to use computers to help verify my reasoning.

Today computer verification looks completely practical to many people who work on
univalent foundation and homotopy type theory.
The road block to this not happening sooner,
was that the foundations of mathematics
was not written in a formal language that could be encoded.

Foundations started with ZFC
Category theory was trying to be the new foundations
Categories are not sets in the next dimension
"sets in the next dimension" are groupoids
Univalent Foundations, is like ZFC and unlike Category Theory in that it is a complete foundational system.
The formal deduction system of Univalent Foundations is the Calculus of Inductive Constructions

I now do my mathematics with a proof assistant.
don't have to worry about mistakes in my arguments
don't have to convince others that my arguments are correct.
just trust the computer.

# Brainstorm Notes

You can embed logic in type theory
inhabitants of a type are the same as a proof of a proposition

If you can think of a proposition you can translate it into a concrete type
This is something you can use

The proofs are rigourous.

It doesn't take much to get started.

Encoding your theorems as types, actually gives you some utility, unlike other encoding in math.

Need to show some type theory, just enough to understand the type annotations of functions.

Constructivity, is not just a hobby

pointers to what people have proved with Coq
Now we know these proofs are absolutely correct:
  - four color graph theorem
  - What has been proved in Lean?

Would breakout groups help to create bigger motivation
So in groups more questions could be answered.

The field is limited in how creative it can be, by its tooling.

Category Theory was really hipster 15 years ago,
but Homotopy type Theory is the new hipster thing.

Mathematics is all about showing things are the same.

It is not just about finding the bugs
it is also about crystalizing the understanding
You can step through the understanding again in Coq
 - professionals

Hott couldn't have come up with the ideas,
without formalising it in Coq.

It is better to appeal to people's laziness,
than their better nature.
Rather show off the automatic teaching assistant
and understanding the paper.

You can have an automatic teaching assistant for
teaching demorgans law.
including automatic grading.
I don't have to put my hand up and ask a question.

There are examples of:
  - applied math in UK somewhere using Coq - George

## Links

  - Gödel numbering: https://en.wikipedia.org/wiki/G%C3%B6del_numbering

  - [Five stages of constructive mathematics](https://www.ams.org/journals/bull/2017-54-03/S0273-0979-2016-01556-4/S0273-0979-2016-01556-4.pdf)
   --- bit off-topic, but maybe something to say about constructive mathematics?

Theoretical:
  - Martin-Lof "Constructive Mathematics and Computer Programming" https://www.cs.tufts.edu/~nr/cs257/archive/per-martin-lof/constructive-math.pdf. 
  - LESS IMPORTANT: Martin-Lof "Intuitionistic Type Theory" http://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf: How Type Theory is a promising new foundation for mathematics, from the 80s, before Univalent Foundations showed the reach of the approach

  - Voevodsky https://www.youtube.com/watch?v=E9RiR9AcXeE
    Proofs have bugs

  - Introduction in Hott book
  We can have some you can write down
  That is very easy to translate into Coq
  They want a language in which they write things that are very formal.
  
  - unimath

## Maps

in math
a -> b -> c = a -> b /\ b -> c
in coq
a -> b -> c = (a, b) -> c
explain currying

but also:
in math, a -> b denotes a map from a to b
in coq, it denotes the type of maps from a to b

## Examples

odd and even is possibly a good example
It allows you to bring in exists and forall

Just resolving implications.
Proving logical laws.
Demorgen's laws.
including exists and forall

Proof something by induction.
sum 0 to n = n (n + 1)/2

0 .. 10
pair them up
(1, 10) (2, 9) (3, 8)
all equal 11 or n + 1
there are n/2 number of these pairs
so sum 0 to n = n (n + 1)/2

# Proving theorems and certifying programs with Coq by Stephan Boyer

https://www.youtube.com/watch?v=VEMFPK5NMhw

My notes:
programming is proofs
Propositions are types
This is the curry howard isomorphism

Logical reasoning is hard
every logical step has a probability of making a mistake

Lemmas are helper functions
collaborate on proofs on github
CI checks that pull requests are correct

implication is a function

Coq is functional programming language with dependent types
quantified proposition is a dependent type

add_assoc
x + (y + z) = (x + y) + z
easy induction and cbn example

all proofs are checked by the core algorithm, which is based on the calculus of induction construction

geekiest computer game

the whole comp cert C compiler was extracted from Coq

Other languages:
  - Agda
  - Lean
  - Idris
  - Isabella

# Martin Lof Notes

Martin-Lof "Constructive Mathematics and Computer Programming" https://www.cs.tufts.edu/~nr/cs257/archive/per-martin-lof/constructive-math.pdf

This included some nice quotable things at the start

"""
 intuitionistic type theory - Martin-Lof
 
 paraphrashed: classical mathematics misses the notion of uncomputable functions

 intuitionists (or constructivists, I shall use these terms synonymously)

 constructive mathematics and programming are essentially the same

  paraprashed: the programmer’s insists that his programs be written in a formal notation
 so that they can be read and executed by a machine

 constructive mathematics as practised by BISHOP  for example, the computational procedures
(programs) are normally left implicit in the proofs, so that considerable
further work is needed to bring them into a form which makes them fit
for mechanical execution
""""


