1. Theorem proving in Lean4: proved Schur decomposition (currently, I am upstreaming it to Mathlib, but it is already available in PhysLean) and that the spin homomorphism has determinant 1. I authored these 2 modules; click on the source links on the document pages:
https://heplean.com/docs/PhysLean/Mathematics/SchurTriangulation.html
https://heplean.com/docs/PhysLean/Lorentz/SL2C/SelfAdjoint.html

2. Functional programming in Lean4: implement a regular expression matcher that is proven to be correct.
https://github.com/kuotsanhsu/software-foundations-lean4/blob/e1a870cd0076de9d3852431320a07de772e6424d/FormalLanguage/Derivative.lean#L148

3. Functional and meta-programming in Lean4: implement custom structure-like commands, `informal_definition` and `informal_lemma`, that can be collected into a dependency graph in SVG format as shown below
https://heplean.com/InformalGraph.html
https://github.com/HEPLean/PhysLean/blob/f8f94979ab03168a3a1c1c430c552dd3dea12f21/HepLean/BeyondTheStandardModel/GeorgiGlashow/Basic.lean
https://github.com/HEPLean/PhysLean/blob/f8f94979ab03168a3a1c1c430c552dd3dea12f21/HepLean/Meta/Informal/Basic.lean
https://github.com/HEPLean/PhysLean/blob/f8f94979ab03168a3a1c1c430c552dd3dea12f21/scripts/MetaPrograms/informal.lean
