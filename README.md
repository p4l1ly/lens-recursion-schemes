Lens Recrusion Schemes
======================

This library has begun with the goal of enriching the area of applicability of
recursion schemes in Haskell to be able to handle mutual recursion and DAG-like
(or graph-like) data structures. Its purpose was to provide an interface, as
uniform as possible, to traversing recursive data structures represented in
various ways. It has however evolved to something a bit less organized but more
practical for the project
[automata-safa](https://github.com/p4l1ly/automata-safa). It includes some
commonly used monads for DAG construction and structural hashing. It also
includes a GrowableArray which grows in a way similar to C++ vectors.

In the tests you can see plate based approach to create something like
Traversal class but for types where recursion can happen elsewhere than in the
last type parameter. You can see this approach applied more thoroughly in the
automata-safa project.

In the automata-safa project, I have come across some performance drawbacks of
recursion implemented via this library, so it is not used in critical places.
Maybe the performance problems can be resolved in some way but I have pushed
the optimization and prettification of this library to my lower priorities by the
time.
