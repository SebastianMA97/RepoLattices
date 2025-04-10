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
  l3 : forall a : A, j a a = a;
  l3d : forall a : A, m a a = a;
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


Definition nord {A : Set} `{LatticeAlg A} (a b : A) := j a b = b.

Lemma AlgToSetReflex `{LatticeAlg A} : Reflexive nord.
Proof.
unfold Reflexive. unfold nord.
intro.
apply (l3 x).
Qed.


Lemma AlgToSetAntisym {A : Set} `{LatticeAlg A} : forall x y : A, nord x y -> nord y x -> x = y.
Proof.
unfold nord.
intros.
rewrite l2 in H1.
rewrite H1 in H0.
assumption.
Qed.


Lemma AlgToSetTrans `{LatticeAlg A} : Transitive nord.
Proof.
unfold Transitive. unfold nord.
intros.
rewrite <- H1.
rewrite <- H0 at 2.
symmetry.
apply l1.
Qed.

Lemma AlgToSet_joinAlg `{LatticeAlg A} : forall x y : A, forall z : A, (nord x z /\ nord y z <-> nord (j x y) z).
Proof.
intros. 
split.
  * unfold nord. intros.
    destruct H0.
    rewrite <- H0 at 2.
    rewrite <- H1 at 2.
    apply l1.
  * intros.
    assert (forall a b : A, (nord a (j a b)) /\ (nord b (j a b))).
      + intros.
        split.
          ++ unfold nord.
             rewrite <- l1.
             rewrite (l3 a).
             reflexivity.
          ++ unfold nord.
             rewrite l2.
             rewrite l1.
             rewrite l3.
             reflexivity.
      + assert (Transitive nord).
          apply AlgToSetTrans.
        unfold Transitive in H2.
        destruct (H1 x y).
        split.
          ++ apply (H2 x (j x y) z).
             assumption.
             assumption.
          ++ apply (H2 y (j x y) z).
             assumption.
             assumption.
Qed.

Lemma AlgToSet_meetAlg `{LatticeAlg A} : forall x y : A, forall z : A, (nord z x /\ nord z y <-> nord z (m x y)).
Proof.
intros. 
split.
  * unfold nord. intros.
    destruct H0.
    rewrite AlgToSet1.
    rewrite AlgToSet1 in H0.
    rewrite AlgToSet1 in H1.
    rewrite l2d.
    rewrite <- H0 at 2.
    rewrite l2d in H1.
    rewrite <- H1 at 2.
    symmetry. rewrite <- l2d.
    symmetry. apply l1d.
  * intros.
    assert (forall a b : A, (nord (m a b) a) /\ (nord (m a b) b)).
      + intros.
        split.
          ++ unfold nord.
             rewrite AlgToSet1.
             rewrite <- l2d.
             rewrite <- l1d.
             rewrite (l3d a).
             reflexivity.
          ++ unfold nord.
             rewrite AlgToSet1.
             rewrite l1d.
             rewrite l3d.
             reflexivity.
      + assert (Transitive nord).
          apply AlgToSetTrans.
        unfold Transitive in H2.
        destruct (H1 x y).
        split.
          ++ apply (H2 z (m x y) x).
             assumption.
             assumption.
          ++ apply (H2 z (m x y) y).
             assumption.
             assumption.
Qed.


Infix "≼" := nord (at level 50).

Class LatticeNord (A : Set) `{LatticeAlg A} := {

  meetN : A -> A -> A;
  joinN : A -> A -> A;

  MHN : forall a b : A,
  forall x, x ≼ a /\ x ≼ b <-> x ≼ (meetN a b);

  JHN : forall a b : A,
  forall x, a ≼ x /\ b ≼ x <-> (joinN a b) ≼ x;

}.

Lemma join_eq (A : Set) `{LatticeAlg A} `{LatticeNord A} : forall a b : A,  j a b = joinN a b.
Proof.
intros.
apply AlgToSetAntisym.
  * apply AlgToSet_joinAlg.
    assert (joinN a b ≼ joinN a b).
      apply AlgToSetReflex.
    apply JHN in H2.
    assumption.
  * apply JHN.
    assert (j a b ≼ j a b).
      apply AlgToSetReflex.
    apply AlgToSet_joinAlg in H2.
    assumption.
Qed.

Lemma meet_eq (A : Set) `{LatticeAlg A} `{LatticeNord A} : forall a b : A,  m a b = meetN a b.
Proof.
intros.
apply AlgToSetAntisym.
  * apply MHN.
    assert (m a b ≼ m a b).
      apply AlgToSetReflex.
    apply AlgToSet_meetAlg in H2.
    assumption.
  * apply AlgToSet_meetAlg.
    assert (meetN a b ≼ meetN a b).
      apply AlgToSetReflex.
    apply MHN in H2.
    assumption.
Qed.

Variables L K : Set.
Variable f : L -> K.

Definition ordPreserv `{Lattice L} `{Lattice K}  := forall a b : L, a ≤ b -> (f a) ≤ (f b).

Definition ordEmmbed `{Lattice L} `{Lattice K}  := forall a b : L, a ≤ b <-> (f a) ≤ (f b).

Definition Biyective `{Lattice L} `{Lattice K} := (forall a b : L, (f a) = (f b) <-> a = b) /\ (forall b : K, (exists a : L, b = f a )).

Definition ordIso `{Lattice L} `{Lattice K} := Biyective /\ ordEmmbed .

Definition joinOrdPreserv `{Lattice L} `{Lattice K} := forall x y : L, ((f x) ⊔ (f y)) ≤ (f (x ⊔ y)) .

Definition meetOrdPreserv `{Lattice L} `{Lattice K} := forall x y : L, (f (x ⊓ y)) ≤ ((f x) ⊓ (f y)) .

Definition joinPreserv `{Lattice L} `{Lattice K} := forall x y : L, ((f x) ⊔ (f y)) = (f (x ⊔ y)).

Definition meetPreserv `{Lattice L} `{Lattice K} := forall x y : L, (f (x ⊓ y)) = ((f x) ⊓ (f y)) .

Definition latticeIso `{Lattice L} `{Lattice K} := joinPreserv /\ meetPreserv /\ Biyective.

Lemma prop219i1 `{Lattice L} `{Lattice K} : ordPreserv  <-> joinOrdPreserv.
Proof.
split.
  * unfold ordPreserv. unfold joinOrdPreserv.
    intros.
    assert (x ≤ x ⊔ y  /\ y ≤ x ⊔ y).
      apply ab_leq_jab.
    destruct H2.
    apply H1 in H2.
    apply H1 in H3.
    assert (f x ≤ f (x ⊔ y) /\ f y ≤ f (x ⊔ y)).
      split.
        assumption.
        assumption.
    apply JH.
    assumption.
  * unfold ordPreserv. unfold joinOrdPreserv.
    intros.
    apply ConnectJ in H2.
    assert (f a ⊔ f b ≤ f (a ⊔ b)).
      apply H1.
    rewrite H2 in H3.
    assert (f a ≤ f a ⊔ f b ).
      apply ab_leq_jab.
    apply (transitive (f a) (f a ⊔ f b) (f b) ).
    assumption.
    assumption.
Qed.



Lemma prop219i2 `{Lattice L} `{Lattice K} : ordPreserv <-> meetOrdPreserv.
Proof.
split.
  * unfold ordPreserv. unfold meetOrdPreserv.
    intros.
    assert (x ⊓ y ≤ x /\ x ⊓ y ≤ y ).
      apply mab_leq_ab.
    destruct H2.
    apply H1 in H2.
    apply H1 in H3.
    apply MH.
    split.
    assumption.
    assumption.
  * unfold ordPreserv. unfold meetOrdPreserv.
    intros.
    apply ConnectM in H2.
    assert (f (a ⊓ b) ≤ f a ⊓ f b).
      apply H1.
    rewrite H2 in H3.
    assert (f a ⊓ f b ≤ f b).
      apply mab_leq_ab.
    apply (transitive (f a) (f a ⊓ f b) (f b) ).
    assumption.
    assumption.
Qed.


Lemma prop219i3 `{Lattice L} `{Lattice K} : ordIso <-> latticeIso.
Proof.
split.
  * unfold ordIso. unfold Biyective.
    intros.
    destruct H1.
    destruct H1.
    unfold latticeIso.
    split.
      ** unfold joinPreserv.
         intros.
         apply antisymmetric.
            + assert (ordPreserv <-> joinOrdPreserv).
                apply (prop219i1).
              destruct H4. 
              assert (ordEmmbed -> ordPreserv).        (* Poner esta prueba al principio *)
                unfold ordEmmbed. unfold ordPreserv.
                intros.
                apply H6.
                assumption.
              apply H6 in H2.
              apply H4 in H2.
              apply H2.
            + assert (exists a : L, (f x ⊔ f y) = f a).
                apply H3.
              destruct H4.
              assert (f x ≤ f x ⊔ f y /\ f y ≤ f x ⊔ f y).
                apply ab_leq_jab.
              rewrite H4 in H5.
              destruct H5.
              apply H2 in H5.
              apply H2 in H6.
              rewrite H4.
              apply H2.
              apply JH.
              split.
              assumption.
              assumption.
      ** split.
           + unfold meetPreserv.
             intros.
             apply antisymmetric.
              ++ assert (ordPreserv <-> meetOrdPreserv).
                   apply prop219i2.
                 destruct H4.
                 assert (ordEmmbed -> ordPreserv).
                  unfold ordEmmbed. unfold ordPreserv.
                  intros.
                  apply H6.
                  assumption.
                 apply H6 in H2.
                 apply H4 in H2.
                 apply H2.
              ++ assert (exists a : L, (f x ⊓ f y) = f a).
                 apply H3.
                 destruct H4.
                 assert (f x ⊓ f y ≤ f x /\ f x ⊓ f y ≤ f y ).
                  apply mab_leq_ab.
                 rewrite H4 in H5.
                 destruct H5.
                 apply H2 in H5.
                 apply H2 in H6.
                 rewrite H4.
                 apply H2.
                 apply MH.
                 split.
                 assumption.
                 assumption.
           + unfold Biyective.
             split.
             assumption.
             assumption.
  * unfold latticeIso. 
    intros.
    unfold ordIso.
    destruct H1.
    destruct H2.
    split.
      ** assumption.
      ** unfold ordEmmbed.
         intros.
         unfold joinPreserv in H1.
         split.
          + intros.
            apply ConnectJ in H4.
            destruct H3.
            apply H3 in H4.
            rewrite <- H1 in H4.
            assert (f a ≤ f a ⊔ f b).
              apply (ab_leq_jab).
            rewrite H4 in H6.
            assumption.
          + intros.
            apply ConnectJ in H4.
            rewrite H1 in H4.
            destruct H3.
            apply H3 in H4.
            apply ConnectJ in H4.
            assumption.
Qed.


