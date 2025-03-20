Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Setoid.

Generalizable All Variables.

Class Poset (A : Set) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

Class Lattice (A : Set) (P: Poset A) := {

  (* Meet and join take two elements of the set A and output another*)
  meet : A -> A -> A;
  join : A -> A -> A;

  (* Meet is equivalent to the infimum*)
  MH : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ (meet a b);

  (* Join is equivalent to the supremum*)
  JH : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> (join a b) ≤ x;

}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).

Section LatticeProperties.

Lemma mab_leq_ab `{Lattice A}: forall a b : A, a ⊓ b ≤ a /\ a ⊓ b ≤ b.
Proof.
  intros.
  apply MH.
  reflexivity.
Qed.

Lemma ab_leq_jab `{Lattice A}: forall a b : A, a ≤ a ⊔ b  /\ b ≤ a ⊔ b.
Proof.
  intros.
  apply JH.
  reflexivity.
Qed.

Theorem L1d `{Lattice A}: forall a b c:A, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof.
  intros.
  apply antisymmetric.
  
  apply MH. split.
    apply transitivity with (y := a ⊓ b). apply mab_leq_ab. apply mab_leq_ab.
    apply MH. split. 
      apply transitivity with (y := a ⊓ b). apply mab_leq_ab. apply mab_leq_ab.
      apply mab_leq_ab.

  apply MH. split.  apply MH.  split.
    apply mab_leq_ab. 
    apply transitivity with (y := b ⊓ c). apply mab_leq_ab. apply mab_leq_ab.
    apply transitivity with (y := b ⊓ c). apply mab_leq_ab. apply mab_leq_ab.
Qed.

Theorem L2d `{Lattice A}: forall a b:A, a ⊓ b = b ⊓ a.
Proof.
  intros.
  apply antisymmetric.
  rewrite <- MH.
  split.
  apply mab_leq_ab.  apply mab_leq_ab.

  rewrite <- MH.
  split.
  apply mab_leq_ab.  apply mab_leq_ab.
Qed.

Theorem  L3d `{Lattice A}: forall a : A, a ⊓ a = a.
Proof.
  intros.
  apply antisymmetric.
  apply mab_leq_ab.  
  apply MH.  split.  reflexivity.  reflexivity.
Qed.

Theorem L4d `{Lattice A}: forall a b : A, a ⊓ (a ⊔ b) = a.
Proof.
  intros.
  apply antisymmetric.
  apply mab_leq_ab.
  apply MH.  split.  reflexivity. apply ab_leq_jab.
Qed.


Theorem L1 `{Lattice A}: forall a b c : A,  (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
  intros.
  apply antisymmetric.
  apply JH. split.
    apply JH. split.  apply ab_leq_jab.
    apply transitivity with (y := b ⊔ c). apply ab_leq_jab. apply ab_leq_jab. 
    apply transitivity with (y := b ⊔ c). apply ab_leq_jab. apply ab_leq_jab. 
  apply JH. split.
    apply transitivity with (y := a ⊔ b). apply ab_leq_jab. apply ab_leq_jab. 
    apply JH.  split. 
      apply transitivity with (y := a ⊔ b). apply ab_leq_jab. apply ab_leq_jab. 
      apply ab_leq_jab.



Qed.

Theorem L2 `{Lattice A}: forall a b : A, a ⊔ b = b ⊔ a.
Proof.
  intros.
  apply antisymmetric.
  rewrite <- JH.
  split.
  apply ab_leq_jab.  apply ab_leq_jab.

  rewrite <- JH.
  split.
  apply ab_leq_jab.  apply ab_leq_jab.
Qed.

Theorem L3 `{Lattice A}: forall a : A, a ⊔ a = a.
Proof.
  intros.
  apply antisymmetric.
  apply JH.  split.  reflexivity.  reflexivity.
  apply ab_leq_jab.  
Qed.

Theorem L4 `{Lattice A}: forall a b : A, a ⊔ (a ⊓ b) = a.
Proof.
  intros.
  apply antisymmetric.
  apply JH.  split.  reflexivity. apply mab_leq_ab.
   apply ab_leq_jab.
Qed.

Lemma ConnectJ `{Lattice A}: forall a b : A, a ≤ b <-> a ⊔ b = b.
Proof.
  intros.  split.
    intros. apply antisymmetric. apply JH. split. assumption. reflexivity. apply ab_leq_jab.
    intros. rewrite <- H0.  apply ab_leq_jab.
Qed.


Lemma  ConnectM `{Lattice A}: forall a b : A, a ≤ b <-> a ⊓ b = a.
Proof.
  intros.  split.
    intros. apply antisymmetric. apply mab_leq_ab. apply MH. split.  reflexivity. assumption.
    intros. rewrite <- H0.  apply mab_leq_ab.
Qed.


Lemma connecting_lemma_joinmeet `{Lattice A}: forall a b : A, a ⊔ b = b <-> a ⊓ b = a.
Proof.
  intros.  split.
    intros. apply  ConnectM. apply ConnectJ. assumption.
    intros. apply ConnectJ. apply  ConnectM. assumption.
Qed.


Theorem connecting_lemma `{Lattice A}: forall a b : A, (a ≤ b <-> a ⊔ b = b) /\  (a ⊔ b = b <-> a ⊓ b = a) /\ (a ⊓ b = a <-> a ≤ b).
Proof.
  intros. 
  split.  apply ConnectJ.
  split. apply connecting_lemma_joinmeet.
  symmetry. apply  ConnectM.
Qed.

Class LatticeAlg (A : Set) := {

  m : A -> A -> A;
  j : A -> A -> A;
  l1 : forall a b c : A, j (j a b) c = j a (j b c);
  l1d : forall a b c : A, m (m a b) c = m a (m b c);
  l2 : forall a b : A, j a b = j b a;
  l2d : forall a b : A, m a b = m b a;
  l3 : forall a b : A, j a a = a;
  l3d : forall a b : A, m a a = a;
  l4 : forall a b : A, j a (m a b) = a;
  l4d : forall a b : A, m a (j a b) = a

}.

Lemma AlgToSet1 `{LatticeAlg A} : forall a b : A, (j a b = b) <-> (m a b = a).
Proof.
split.
  intro.
  rewrite <- H0.
  apply l4d.
intro.
rewrite l2d in H0. rewrite <- H0.
rewrite l2. apply (l4 b a ).
Qed.


Definition nord `{LatticeAlg A} := forall a b : A, j a b = b.



