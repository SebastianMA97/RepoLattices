From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.

Lemma dobl (A : Prop) :  A <-> A /\ A.
Proof.
split. by [].
move=> [h1 h2]; by [].
Qed.

Definition reflexive {T : Type} (rel : T -> T -> Prop) : Prop := forall x :T, rel x x.
Definition antisymetric {T : Type} (rel : T -> T -> Prop) : Prop := forall x y : T, (rel x y) /\ (rel y x) <-> (x = y).
Definition transitive {T : Type} (rel : T -> T -> Prop) :Prop := forall x y z :T, rel x y -> rel y z -> rel x z.


Structure quasiOrder := QuasiOrder
  { 
    Qo :> Type;
    orden : Qo -> Qo -> Prop;
    reflexq : reflexive orden;
    antisymq : antisymetric orden;
    transq : transitive orden
   }.
Notation "x ≤ y" := (orden _ x y) (at level 50).
Notation ρ := (reflexq _).
Notation τ := (transq _).
Notation antisym := (antisymq _).


Structure semiLattice := SemiLattice 
  { 
    SL :> quasiOrder;
    m : SL -> SL -> SL;
    LambdaK : forall a b : SL, m a b ≤ a;
    LambdaK' : forall a b : SL, m a b ≤ b;
    LambdaS : forall c a b : SL,  (c ≤ a /\ c ≤ b) -> c ≤ ( m a b)
   }.
Notation "x ∧ y" := (@m _ x y) (at level 49). (* \wedge *)
Notation ΛK := (@LambdaK _).
Notation ΛK' := (@LambdaK' _).
Notation ΛS := (@LambdaS _).

Theorem ΛW {S : semiLattice} : forall a: S, a ≤ a ∧ a.
Proof.
move=> a.
move: (ρ a)=> H.
move: (conj H H).
by move=> /ΛS.
Qed.

Theorem ΛC {S : semiLattice} : forall a b : S, a ∧ b ≤ b ∧ a.
Proof.
move=> a b.
move: (ΛK' a b)=> H0.
move: (ΛK a b)=> H1.
move: (conj H0 H1).
by move=> /ΛS.
Qed.

Theorem ΛB {S : semiLattice} : forall a b c : S, a ≤ b -> c ∧ a ≤ c ∧ b.
Proof.
move=> a b c H.
move: (ΛK c a)=> H0.
move: (τ _ _ _ (ΛK' c a) H)=> H1.
move: (conj H0 H1).
by move=> /ΛS.
Qed.

Theorem ΛB' {S : semiLattice} : forall a b c : S, a ≤ b -> a ∧ c ≤ b ∧ c.
Proof.
move=> a b c H.
move: (ΛB a b c H).
move: (ΛC a c)=> H0.
move: (ΛC c b)=> H1.
move=> /(τ _ _ _ H0)=> H2.
by move: (τ _ _ _ H2 H1).
Qed.

Theorem C3i {S : semiLattice} : forall a : S, a ∧ a = a.
Proof.
move=> a.



Theorem RpJ {T : lattice}: forall a b c : T, a ≤ b -> c ⊔ a ≤ (c ⊔ b).
Proof.
move=> a b c H.
rewrite -JH.
split.
  by move: (ab_leq_jab c b) => /proj1.
move: (ab_leq_jab c b) => /proj2.
move: H.
by apply: trans.
Qed.

Theorem RpM {T : lattice}: forall a b c : T, a ≤ b -> c ⊓ a ≤ (c ⊓ b).
Proof.
move=> a b c H.
rewrite -MH.
split.
  by move: (mab_leq_ab c a) => /proj1.
move: H.
move: (mab_leq_ab c a) => /proj2.
by apply: trans.
Qed.

Lemma siml {T : lattice} :  forall a b : T, a = b -> a ≤ b.
Proof.
move=> x y Hip.
rewrite Hip.
move: (reflex y)=>H.
by [].
Qed.

Lemma simr {T : lattice} :  forall a b : T, a = b -> b ≤ a.
Proof.
move=> x y Hip.
rewrite Hip.
move: (reflex y)=>H.
by [].
Qed.


Lemma mW {T : lattice} : forall a : T, a ≤ (a ⊓ a).
Proof.
move=> a.
move: (reflex a)=> H.
rewrite -MH.
by split.
Qed.

Lemma jW {T : lattice} : forall a : T, a ⊔ a ≤ a.
Proof.
move=> a.
move: (reflex a)=> H.
rewrite -JH.
by split.
Qed.


Theorem Curry4B_7 {T : lattice} : (forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ c)) 
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite /Distributive => H.
  move=> a b c.
  move: (H a b c) => /siml-H1.
  move: (mab_leq_ab a c) => /proj2 /(RpJ _ _ (a ⊓ b)).
  move: H1.
  apply: trans.
move=> H a b c.
move: (mab_leq_ab a (b ⊔ c)) => /proj1-H0.
move: (conj H0 (H a b c)).
rewrite MH [(a ⊓ b) ⊔ c]L2 => H1.
move: (H a c (a ⊓ b))=> H2.
move: (trans _ _ _ H1 H2).
rewrite [(a ⊓ c) ⊔ (a ⊓ b)]L2 => H3.
move: (Lema4_1i a b c) => H4.
by move: (antisym _ _ H4 H3).
Qed.


(*
  rewrite /Distributive => H.
  move=> a b c.
  have sim:  forall a b : T, a = b -> a ≤ b.
    move=> x y Hip; rewrite Hip; apply: reflex.
  have Hip :forall a b c : T, (a ⊓ b) ⊔ (a ⊓ c) ≤ ((a ⊓ b) ⊔ c).
    move=> x y z.
    rewrite -JH.
    split.
      by move: (ab_leq_jab (x ⊓ y) z ) => /proj1.
    move: (ab_leq_jab (x ⊓ y) z) => /proj2.
    move: (mab_leq_ab x z) => /proj2.
    by apply: trans.
  move: (H a b c) (Hip a b c).
  move=> /sim.
  apply: trans.
move=> H.
have Hip1: forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ (a ⊓ c)).
move=> a b c.
have Hip : forall a b c : T, (a ⊓ ((a ⊓ b) ⊔ c)) ≤ ((a ⊓ b) ⊔ (a ⊓ c)).
  move=> x y z.
  rewrite [(x ⊓ y) ⊔ z]L2 [(x ⊓ y) ⊔ (x ⊓ z)]L2.
  by move: (H x z (x ⊓ y)).
apply: (trans _ (a ⊓ ((a ⊓ b) ⊔ c)) _ ); last first.
 by [].
rewrite -MH.
split; last first.
  by [].
by move: (mab_leq_ab a ((b ⊔ c))) => /proj1.
move=> a b c.
apply: antisym.
  by [].
by move: (Lema4_1i a b c).
Qed.
*)



Theorem Curry4B_9 {T : lattice} : (forall a b c : T, (a ⊓ b ≤ c /\ a ≤ (b ⊔ c)) -> (a ≤ c))
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite -Curry4B_7 => H.
  move=> a b c [H0 H1].
  move: (mW a)=> H2.
  move: (RpM _ _ a H1) => H3.
  move: (trans _ _ _ H2 H3)=> H4.
  move: (trans _ _ _ H4 (H a b c)) => H5.
  move: (RpJ _ _ c H0).
  rewrite L2 => H6.
  move: (trans _ _ _ H6 (jW c)) => H7.
  by move: (trans _ _ _ H5 H7).
move => H.
have aux :forall a b c : T, a ⊓ (b ⊔ c) ≤ ((a ⊓ b) ⊔ c).
move=> a b c.
move: (ab_leq_jab (a ⊓ b) c) => /proj1.
rewrite -{1}(L4d b c) [b ⊓ (b ⊔ c)]L2d -L1d => H0.
move: (mab_leq_ab a (b ⊔ c)) => /proj2.
rewrite -{2}(L4 b a) [b ⊓ a]L2d L1 => H1.
by move: (H _ _ _ (conj H0 H1)).
move: (@Curry4B_7 T) => [Cr Cl].
apply: Cr.
by [].
Qed.

(*
split; last first.
  rewrite -Curry4_7 => H.
  move=> a b c [H0 H1].
  have aux1 : a ⊓ (b ⊔ c) ≤ c.
    apply: (trans _ ((a ⊓ b) ⊔ c)).
      by [].
    rewrite -JH.
    split.
      by [].
    by apply: reflex.
  apply: (trans _ (a ⊓ (b ⊔ c))); last first.
    by [].
  rewrite -MH.
  split; last first.
    by [].
  by apply: reflex.
move=> H.
rewrite -Curry4_7.
move=> a b c.
apply: (H _ b).
  split.
  rewrite L1d [_ ⊓ b]L2d L4d.
  by move: (ab_leq_jab (a ⊓ b) c) => /proj1.
rewrite -L1 [a ⊓ b]L2d L4.
by move: (mab_leq_ab a (b ⊔ c) ) => /proj2. 
Qed.
*)

Lemma Curry4B_91 {T : lattice} : (forall a b c : T, (a ⊓ c ≤ (b ⊓ c) /\ a ⊔ c ≤ (b ⊔ c)) -> (a ≤ b))
                                 <-> (@Distributive T).
Proof.
rewrite -Curry4B_9.
split.
  move => H.
  move => a c b.
  move: (H a b c).
  rewrite -MH -JH [c ⊔ b]L2 => H0 [H1 H3].
  move: (mab_leq_ab a c) => /proj2-H2.
  move: (ab_leq_jab b c) => /proj2-H4.
  apply: H0.
  split.
    by split.
  by split.
move => H a c b.
rewrite -MH -JH.
move=> [[H0 H1] [H2 H3]].
apply: (H a b c).
rewrite [b ⊔ c]L2.
by split.
Qed.

Lemma Curry4B_92 {T : lattice} : (@Distributive T)
                -> (forall a b c : T, (a ⊓ c = (b ⊓ c) /\ a ⊔ c = (b ⊔ c)) -> (a = b)).
Proof.
rewrite -Curry4B_91 => H.
move=> a b c /dobl.
move=> [[/(siml _ _)-H0 /(siml _ _)H1] [/(simr _ _)-H2 /(simr _ _)H3]].
apply: antisym.
apply: (H a b c).
by split.
apply: (H b a c).
by split.
Qed.

Structure implicativeLattice := ImplicativeLattice 
  {
    ImpL :> lattice;
    ply : ImpL -> ImpL -> ImpL;
    Imp_P1 : forall a b : ImpL, a ⊓ (ply a b) ≤ b;
    Imp_P2 : forall a b c : ImpL, a ⊓ c ≤ b -> c ≤ (ply a b)
  }.
Notation "x ⊃ y" := (@ply _ x y) (at level 50). (* \supset *)
Notation P1 := (Imp_P1 _).
Notation P2 := (Imp_P2 _).

(* Sección 4C Curry *)

Theorem Curry4C_LMono {T : implicativeLattice} : forall a b c: T, a ≤ b -> (b ⊃ c) ≤ (a ⊃ c).
Proof.
move=> a b c H.
move: (RpM _ _ (b ⊃ c) H).
rewrite L2d [_⊓ b]L2d => H0.
move: (P1 b c) => H1.
move: (trans _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem Curry4C_RMono {T : implicativeLattice} : forall a b c: T, a ≤ b -> (c ⊃ a) ≤ (c ⊃ b).
Proof.
move=> a b c H1.
move: (P1 c a)=> H0.
move: (trans _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem Curry4C_Unidad {T : implicativeLattice} : forall a : T, exists u, a ≤ u.
Proof.
move=> a.
move: (mab_leq_ab a a) => /proj1.
move=> /P2-H.
by exists (a⊃a).
Qed.

Theorem Curry4C_1i {T : implicativeLattice} : forall a b : T, b ≤ (a ⊃ b).
Proof.
move=> a b.
by move: (mab_leq_ab a b)=> /proj2 /P2.
Qed.

Theorem Curry4C_1ii1 {T : implicativeLattice} 
        : forall a b c : T, (a ⊃ (b ⊃ c) = (a ⊓ b)⊃ c).
Proof.
move=> a b c.
apply antisym.
  move: (P1 a (b ⊃ c)).
  move=> /(RpM _ _ b).
  rewrite -L1d [b ⊓ a]L2d=> H0.
  move: (P1 b c)=> H1.
  move: (trans _ _ _ H0 H1).
  by move=> /P2.
move: (P1 (a ⊓ b) c).
rewrite [_ ⊓ b]L2d L1d.
by move=> /P2 /P2.
Qed.

Theorem Curry4C_1ii2 {T : implicativeLattice} 
        : forall a b c : T, ((a ⊓ b) ⊃ c = b ⊃ (a ⊃ c)).
Proof.
move=> a b c.
move: (Curry4C_1ii1 b a c).
by rewrite L2d.
Qed.