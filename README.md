# Equality
Formalization of type theory with equality defined by recursion on type

# Changelog

* Tue Apr 26:
** Filled in all metas in setoid.agda
** Changed the definition of fibration of setoids over setoids.  Now SubSS* requires that squares of level -1 are mapped to commutative squares of level 0.  (Note: all squares commute at level -1).
** Changed names of modules to begin with a capital letter.
** Divided module prop into submodules.

# To Do

1. Comments in each module giving purpose
1. Divide setoid and groupoid into submodules, using consistent naming
2. Model in setoids of: \lambda\simeq + "equivalence ops"
3. An example of propositional transport?
4. Groupoids!!
5. Model in groupoids of: \lambda\simeq, equivalence ops, implement groupoid ops: refl, sym, trans, assoc, units, etc..
6. Nice example of transport of structure!! (Grothendieck??)
-------------------------
7. (n+1)-groupoids!!!!!!
8. Let n=n+1;
9. Goto 7
-------------------------
10. Take lim_n->oo.