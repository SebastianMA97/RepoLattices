From mathcomp Require Import all_ssreflect.

Definition reflexive {T : Type} (rel : T -> T -> Prop) : Prop := forall x :T, rel x x.
Definition antisymetric {T : Type} (rel : T -> T -> Prop) : Prop := forall x y : T, (rel x y) -> (rel y x) -> (x = y).
Definition transitive {T : Type} (rel : T -> T -> Prop) :Prop := forall x y z :T, rel x y -> rel y z -> rel x z.
Definition order {T : Type} (rel : T -> T -> Prop) := reflexive rel /\ antisymetric rel /\ transitive rel.

Structure ordenParcial := OrdenParcial
  {
    O :> Type;
    ord : O -> O -> Prop;
    reflexT : reflexive ord;
    antisymT : antisymetric ord;
    transT : transitive ord;
  }.
Notation "x ≤ y" := (ord _ x y) (at level 50).

Structure lattice := Lattice 
  { 
    T :> ordenParcial;
    joinT : T -> T -> T;
    jHT : (forall z : T , forall x y : T,  (x ≤ z /\ y ≤ z) <->( joinT x y) ≤ z);
    meetT : T -> T -> T;
    mHT : (forall z : T , forall x y : T,  (z ≤ x /\ z ≤ y) <-> z ≤ ( meetT x y));
  }.

Notation "x ⊓ y" := (@meetT _ x y) (at level 50). (* \sqcap *)
Notation "x ⊔ y" := (@joinT _ x y) (at level 50). (* \sqcup *)
Notation reflex := (reflexT _).
Notation antisym := (antisymT _).
Notation trans := (transT _).
Notation JH := (@jHT _).
Notation MH := (@mHT _).
