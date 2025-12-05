From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.
From ProyectoCoq Require Import Dualidad.
From ProyectoCoq Require Import Ltac_Dual.
From Coq Require Import Logic.


Lemma dobl (A : Prop) :  A <-> A /\ A.
Proof.
split. by [].
move=> [h1 h2]; by [].
Qed.

Lemma ab_leq_jab {T : lattice} (z : T) : forall a b : T ,   a ≤ (a ⊔ b) /\  b ≤ (a ⊔ b).
Proof.
move=> a b.
split.
  by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj1.
by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj2.
Qed.

Lemma mab_leq_ab {T : lattice} (z : T) : forall a b : T ,  (a ⊓ b) ≤ a /\ (a ⊓ b) ≤ b.
Proof.
(* Prueba por dualidad *)
move=> a b.
reflect_goal z [:: a; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ab_leq_jab L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Lemma ConnectJ {T : lattice} (z : T) : forall a b : T ,  a ≤ b <-> (a ⊔ b = b).
Proof.
split.
move=> abLeq.
  apply: antisym.
    rewrite -(JH).
    split.
      by [].
    by apply: reflex.
  move: (reflex (a ⊔ b)).
  by rewrite -(JH) => /proj2.
move=> H.
move: (reflex (a ⊔ b)).
rewrite {2}H.
move: (ab_leq_jab z a b) => /proj1.
by apply: trans.
Qed.

Lemma ConnectM {T : lattice} (z : T) : forall a b : T , a ≤ b <-> (b ⊓ a = a).
Proof.
move=> a b; rewrite /iff.
(* Prueba por dualidad *)
reflect_goal z [:: a; b] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
move: ((@ConnectJ L0 z0 ) (eval L0 z0 env0 (Var 1)) (eval L0 z0 env0 (Var 0)) ).
by rewrite /iff.
Qed.

(* Propiedades L1 a L4*)

Lemma L3 {T : lattice} (z : T) : forall a : T , a ⊔ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /(ConnectJ z).
Qed.

Lemma L3d {T : lattice} (z : T) : forall a : T , a ⊓ a = a.
Proof.
move=> a.
(* Prueba por dualidad *)
reflect_goal z [:: a] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@L3 L0 z0) (eval L0 z0 env0 (Var 0)) ).
Qed.

Lemma L2 {T : lattice} (z : T) : forall a b : T , a ⊔ b = b ⊔ a.
Proof.
move=> a b.
apply: antisym.
  move: (ab_leq_jab z b a) => /and_comm.
  by rewrite JH. 
move: (ab_leq_jab z a b) => /and_comm.
by rewrite JH.
Qed.

Lemma L2d {T : lattice} (z : T) : forall a b : T , a ⊓ b = b ⊓ a.
Proof.
move=> a b.
(* Prueba por dualidad *)
reflect_goal z [:: a; b] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@L2 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Lemma L4 {T : lattice} (z : T) : forall a b : T , a ⊔ (a ⊓ b) = a.
Proof.
move=> a b.
move: (mab_leq_ab z a b) => /proj1.
move=> /(ConnectJ z).
by rewrite L2.
Qed.

Lemma L4d {T : lattice} (z : T) : forall a b : T , a ⊓ (a ⊔ b) = a.
Proof.
move=> a b.
(* Prueba por dualidad *)
reflect_goal z [:: a; b] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@L4 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Lemma L1 {T : lattice} (z : T) : forall a b c : T , (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof. 
have c_leq_jab: forall x y w : T , w ≤ y -> w ≤ (x ⊔ y).
    move=> x y w w_leq_y; move: (ab_leq_jab z x y) => /proj2.
    move: w_leq_y; by apply: trans.
move=> a b c.
apply: antisym.
  rewrite -JH.
  split.
    rewrite -JH.
    split.
      by move: (ab_leq_jab z a (b ⊔ c)) => /proj1. (*1° caso a ≤ sup a (sup b c)*)
    by move: (ab_leq_jab z b c) => /proj1 /c_leq_jab. (*2° caso b ≤ sup a (sup b c)*)
  by move: (ab_leq_jab z b c) => /proj2 /c_leq_jab. (*c ≤ sup a (sup b c)*)
rewrite -JH.
split.
  rewrite (L2 z).
  move: (ab_leq_jab z a b) => /proj1.
  by move=> /c_leq_jab.
rewrite -JH.
split.
  move: (ab_leq_jab z a b) => /proj2; rewrite [_ ⊔ c](L2 z).
  by move=> /c_leq_jab.  (*sup c (sup a b)*)
by move: (ab_leq_jab z (a ⊔ b) c) => /proj2. (*c ≤ sup (sup a b) c*)
Qed.

Lemma L1d {T : lattice} (z : T) : forall a b c : T , (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. 
move=> a b c.
(* Prueba por dualidad *)
reflect_goal z [:: a; b; c] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@L1 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
                      (eval L0 z0 env0 (Var 2)) ).
Qed.

Structure latticeAlg := LatticeAlg 
  {
    A :> Type;
    j : A -> A -> A;
    m : A -> A -> A;
    l1 : forall a b c : A, j (j a b) c = j a (j b c);
    l1d : forall a b c : A, m (m a b) c = m a (m b c);
    l2 : forall a b : A, j a b = j b a;
    l2d : forall a b : A, m a b = m b a;
    l3 : forall a : A, j a a = a;
    l3d : forall a : A, m a a = a;
    l4 : forall a b : A, j a (m a b) = a;
    l4d : forall a b : A, m a (j a b) = a
  }.
Notation "x ∧ y" := (@m _ x y) (at level 50). (* \wedge *)
Notation "x ∨ y" := (@j _ x y) (at level 50). (* \vee *)
Notation L1_Alg := (l1 _).
Notation L1d_Alg := (l1d _).
Notation L2_Alg := (l2 _).
Notation L2d_Alg := (l2d _).
Notation L3_Alg := (l3 _).
Notation L3d_Alg := (l3d _).
Notation L4_Alg := (l4 _).
Notation L4d_Alg := (l4d _).

Canonical Alg_lattice {T : lattice} (z : T) := LatticeAlg T (@joinT T) (@meetT T) (L1 z) (L1d z) (L2 z) (L2d z) (L3 z) (L3d z) (L4 z) (L4d z).

Lemma AlgToSet1 {T : latticeAlg} : forall a b : T, ( a ∨ b = b) <-> ( a ∧ b = a).
Proof.
split.
  move=> jab_b.
  move: (L4d_Alg a b).
  by rewrite jab_b.
move=> mab_a.
move: (L4_Alg b a).
by rewrite L2d_Alg mab_a L2_Alg.
Qed.

Definition nord {T : latticeAlg} (a b : T) := (a ∨ b = b).
Notation "x ≼ y" := (@nord _ x y) (at level 50). (* \preccurlyeq *)

Lemma AlgToSetReflex {T : latticeAlg} : reflexive (@nord T).
Proof.
  move=> a.
  rewrite /nord.
  by apply: L3_Alg.
Qed.

Lemma AlgToSetAntisym {T : latticeAlg} : antisymetric (@nord T).
Proof.
  move=> a b.
  rewrite /nord => supb.
  by rewrite L2_Alg supb.
Qed.

Lemma AlgToSetTrans {T : latticeAlg} : transitive (@nord T).
Proof.
move=> a b c.
rewrite /nord.
move=> supab supbc.
by move: (L1_Alg a b c); rewrite supab supbc.
Qed.

Canonical T_ordenParcial {T : latticeAlg} := OrdenParcial T (@nord T) AlgToSetReflex AlgToSetAntisym AlgToSetTrans.


Lemma AlgToSet_joinAlg {T : latticeAlg} : forall z : T, (forall x y : T, (x ≼ z /\ y ≼ z) <-> (x ∨ y) ≼ z).
Proof.
move=> z x y.
split.
  rewrite /nord.
  move=> [supxz supyz].
  by move: supxz; rewrite -{1}(supyz) -L1_Alg.
move=> H1.
have cotaS: forall a b : T, (a ≼ (a ∨ b)) /\ (b ≼ (a ∨ b)).
  move=> a b.
  split.
    by rewrite /nord -L1_Alg L3_Alg.
  by rewrite /nord L2_Alg L1_Alg L3_Alg.
split.
  move: (cotaS x y) H1 => /proj1.
  by apply: AlgToSetTrans.
move: H1; move: (cotaS x y); move=> /proj2.
by apply: AlgToSetTrans.
Qed.

Lemma AlgToSet_meetAlg {T : latticeAlg}: forall z : T, (forall x y : T, (z ≼ x /\ z ≼ y) <-> z ≼ (x ∧ y) ).
Proof.
move=> z x y.
split.
  rewrite /nord.
  move => [/(AlgToSet1)-H1 /(AlgToSet1)-H2].
  rewrite AlgToSet1.
  move: H1.
  by rewrite -{1}(H2) L1d_Alg (L2d_Alg y x).
move=> H1.
have cotaI: forall a b : T, ((a ∧ b) ≼ a) /\ ((a ∧ b) ≼ b).
  move=> a b.
  split.
    by rewrite /nord AlgToSet1 (L2d_Alg) -(L1d_Alg) L3d_Alg.
  by rewrite /nord AlgToSet1 L1d_Alg L3d_Alg.
split.
  move: (cotaI x y) => /proj1; move: H1. 
  by apply: AlgToSetTrans.
move: (cotaI x y) => /proj2; move: H1.
by apply: AlgToSetTrans.
Qed.

Canonical T_lattice {T : latticeAlg} := Lattice (OrdenParcial T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans)
                       (@j _) AlgToSet_joinAlg (@m _) AlgToSet_meetAlg.

Lemma join_eq {T : latticeAlg}: forall a b : T,  a ∨ b = joinT T_lattice a b.
Proof. by []. Qed.

Lemma meet_eq {T : latticeAlg}: forall a b : T, a ∧ b = meetT T_lattice a b.
Proof. by []. Qed.

(* Proposición 2.19 *)

Definition ordPreserv {L K : lattice} {f : L -> K} 
                      := forall a b : L, a ≤ b -> (f a) ≤ (f b).

Definition ordEmmbed {L K : lattice} {f : L -> K}
                     := forall a b : L, a ≤ b <-> (f a) ≤ (f b).

Definition Biyective {L K : lattice} {f : L -> K}
                     := (forall a b : L, (f a) = (f b) <-> a = b) /\ (forall b : K, (exists a : L, b = f a )).

Definition ordIso {L K : lattice} {f : L -> K} := (@Biyective L K f) /\ (@ordEmmbed L K f) .

Definition joinOrdPreserv {L K : lattice} {f : L -> K}
                          := forall x y : L, (f x) ⊔ (f y) ≤ f (x ⊔ y) .

Definition meetOrdPreserv {L K : lattice} {f : L -> K}
                          := forall x y : L, f (x ⊓ y) ≤ ((f x) ⊓ (f y)).

Definition joinPreserv {L K : lattice} {f : L -> K}
                       := forall x y : L, (f x) ⊔ (f y) = f (x ⊔ y).

Definition meetPreserv {L K : lattice} {f : L -> K}
                       := forall x y : L, f (x ⊓ y) = (f x) ⊓ (f y).

Definition latticeIso {L K : lattice} {f : L -> K}
                      := (@joinPreserv L K f) /\ (@meetPreserv L K f) /\ (@Biyective L K f).

Lemma prop219i1 {L K : lattice} (z : L) (fz : K) {f : L -> K} : (@ordPreserv L K f)  <-> (@joinOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (ab_leq_jab z a b) => [/(ordenP)-cota_fa /(ordenP)-cota_fb].
  rewrite -JH.
  by split.
rewrite /joinOrdPreserv => H.
move=> a b /(ConnectJ z)-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab fz (f a) (f b)) => /proj1.
by apply: trans.
Qed.


Lemma prop219i2 {L K : lattice} (z : L) (fz : K) {f : L -> K} : (@ordPreserv L K f) <-> (@meetOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (mab_leq_ab z a b) => [/ordenP-cota_fa /ordenP-cota_fb].
  move: (conj cota_fa cota_fb).
  by rewrite MH.
rewrite /meetOrdPreserv => H.
move=> a b /(ConnectM z); rewrite (L2d z) => mab_L.
move: (mab_leq_ab fz (f a) (f b)) => /proj2.
move: (H a b); rewrite mab_L.
by apply: trans.
Qed.

Lemma prop219i3 {L K : lattice} (z : L) (fz : K) {f : L -> K} : (@ordIso L K f) <-> (@latticeIso L K f).
Proof.
split.
  rewrite /ordIso /ordEmmbed /Biyective; move=> [[inj sob] H].
  rewrite /latticeIso. 
  split.
    move=> x y; apply: antisym.
      move: (@prop219i1 L K z fz f); rewrite /ordPreserv /joinOrdPreserv => /proj1-H2.
      apply: H2 => c d.
      by move: (H c d) => /proj1.
    move: (sob ((f x) ⊔ (f y))) => [a Ha].
    move: (ab_leq_jab fz (f x) (f y)).
    rewrite Ha; move=> [/H-xleqa /H-yleqa].
    by rewrite -H -JH.
  split.
    move=> x y; apply: antisym.
      move: (@prop219i2 L K z fz f); rewrite /ordPreserv /meetOrdPreserv => /proj1-H2.
      apply: H2 => c d;
      by move: (H c d) => /proj1.
      move: (sob ((f x) ⊓ (f y))) => [a Ha].
      move: (mab_leq_ab fz (f x) (f y)).
      rewrite Ha; move=> [/H-aleqx /H-aleqy].
      by rewrite -H -MH.
    by [].
rewrite /latticeIso; move=> [Hjoin [Hmeet [inj sob]]].
split.
  by [].
move=> a b.
split.
  by move=> /(ConnectJ z) /inj; rewrite -Hjoin -(ConnectJ).
by rewrite (ConnectJ fz) Hjoin inj -(ConnectJ).
Qed.

(* Lattices modulares, distributivas y booleanas *)

Lemma Lema4_1i {T : lattice} (z : T) : forall a b c : T, ((a ⊓ b) ⊔ (a ⊓ c)) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c.
rewrite -MH.
split.
  rewrite -JH.
  split.
    by move: (mab_leq_ab z a b) => /proj1.
  by move: (mab_leq_ab z a c) => /proj1.
rewrite -JH.
move: (ab_leq_jab z b c) => [cota_b cota_c].
split.
  move: (mab_leq_ab z a b) cota_b => /proj2.
  by apply: trans.
move: (mab_leq_ab z a c) cota_c => /proj2.
by apply: trans.
Qed.

Lemma Lema4_1id {T : lattice} (z : T) : forall a b c : T, (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ (a ⊔ c)).
Proof.
move=> a b c.
(* Prueba por dualidad *)
reflect_goal z [:: a; b; c] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@Lema4_1i L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
           (eval L0 z0 env0 (Var 2)) ).
Qed.

Lemma Lema4_1ii {T : lattice} (z : T) : forall a b c : T, c ≤ a -> ((a ⊓ b) ⊔ c) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c /ConnectM- H.
by move: (Lema4_1i z a b c); rewrite H.
Qed.

Lemma Lema4_1iid {T : lattice} (z : T) : forall a b c : T, a ≤ c -> (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ c).
Proof.
move=> a b c.
(* Prueba por dualidad *)
reflect_goal z [:: a; b; c] meetT joinT.
apply reflectDual.
rewrite Dual /dual /dual_t => L0 z0 env0.
rewrite /eval_f.
by move: ((@Lema4_1ii L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
           (eval L0 z0 env0 (Var 2)) ).
Qed.

Lemma Lema4_1iii {T : lattice} (z : T) : forall a b c : T, ((a ⊓ b) ⊔ (b ⊓ c) ⊔ (c ⊓ a)) ≤ ((a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a)).
Proof.
have aux : forall a b c : T, (a ⊓ b) ≤ (c ⊔ a).
  move=> a b c; move: (ab_leq_jab z c a)=> /proj2.
  move: (mab_leq_ab z a b) => /proj1.
  by apply: trans.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    have H1 : b ≤ ((a ⊔ b) ⊓ (b ⊔ c)).
      rewrite -MH.
      split.
        by move: (ab_leq_jab z a b) => /proj2.
      by move: (ab_leq_jab z b c) => /proj1.
    have H2 : ((a ⊓ b) ⊔ (b ⊓ c)) ≤ b.
      rewrite -JH.
      split.
        by move: (mab_leq_ab z a b) => /proj2.
      by move: (mab_leq_ab z b c) => /proj1.
    by move: H1; move: H2; apply: trans.
  rewrite -JH.
  split.
    by apply: aux.
  by rewrite (L2d z) (L2 z); apply aux.
rewrite -MH.
split.
  rewrite -MH.
  split.
    by rewrite (L2d z) (L2 z); apply aux.
  by apply: aux.
by rewrite (L2 z); apply: aux.
Qed.


Lemma Lema4_2i {T : lattice} (z : T) : forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)) <->
                                   (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))).
Proof.
split. 
  by move=> H1 /dobl [/(ConnectM z)-H] /H1; rewrite H.
by move=> H1 /dobl [/(ConnectM z)-H] /H1; rewrite H.
Qed.

Lemma Lema4_2ii {T : lattice} (z : T) : (forall a b c : T, c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))) <->
                  (forall p q r : T, (p ⊓ (q ⊔ (p ⊓ r))) = ((p ⊓ q) ⊔ (p ⊓ r))).
Proof.
split.
  move=> H p q r.
  move: (mab_leq_ab z p r) => /proj1.
  rewrite (Lema4_2i z).
  by apply: H.
move=> H a b c /(ConnectM z)-cleqa.
rewrite -{1}cleqa. 
by apply: H.
Qed.

Lemma Lema4_3 {T : lattice} (z : T) : (forall a b c : T, (a ⊓ (b ⊔ c)) = (a ⊓ b) ⊔ (a ⊓ c)) <-> 
                (forall p q r : T, (p ⊔ (q ⊓ r)) = (p ⊔ q) ⊓ (p ⊔ r)).
Proof.
split.
  move=> H p q r.
  move: (H (p ⊔ q) p r).
  rewrite [(p ⊔ q) ⊓ p](L2d z) [p ⊓ (p ⊔ q)](L4d z) [(p ⊔ q) ⊓ r](L2d z).
  rewrite (H r p q).
  by rewrite -(L1 z) [r ⊓ p](L2d z) [p ⊔ (p ⊓ r)](L4 z) [r ⊓ q](L2d z).
move=> H a b c.
move: (H (a ⊓ b) a c).
rewrite [(a ⊓ b) ⊔ a](L2 z) [a ⊔ (a ⊓ b)](L4 z).
rewrite [(a ⊓ b) ⊔ c](L2 z) (H c a b).
by rewrite -(L1d z) [c ⊔ a](L2 z) [a ⊓ (a ⊔ c)](L4d z) [c ⊔ b](L2 z).
Qed.

Definition Distributive {T : lattice} := forall a b c : T, (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c)).

Definition Modu_L {T : lattice} := forall a b c : T, (c ≤ a -> (c ⊔ (b ⊓ a)) = ((c ⊔ b) ⊓ a)).

Lemma Modular2 {T : lattice} (z : T) : (@Modu_L T) -> (forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c))).
Proof.
rewrite /Modu_L => H a b c.
move=> /(H a b c).
by rewrite (L2 z) [b ⊓_](L2d z) [_ ⊓ a](L2d z) [c ⊔ _](L2 z).
Qed.

Lemma ModularD {T : lattice} (z : T) : (@Modu_L T) -> (forall a b c : T, (a ≤ c -> (a ⊔ (b ⊓ c)) = ((a ⊔ b) ⊓ c)) ).
Proof.
rewrite /Modu_L => H a b c.
by move=>/(H c b a).
Qed.

Lemma ModularD2 {T : lattice} (z : T) : (forall a b c : T, (a ≤ c -> (a ⊔ (b ⊓ c)) = ((a ⊔ b) ⊓ c)))
                -> (forall a b c : T, (a ≤ c -> ( c ⊓ (b ⊔ a)  = (c ⊓ b) ⊔ a ))).
Proof.
move=> H a b c.
move=> /(H _ b).
by rewrite (L2 z) [b ⊓ c](L2d z) [_ ⊓ c](L2d z) [a ⊔ b](L2 z).
Qed.

Structure boundedLattice := BoundedLattice 
  {
    BL :> lattice;
    Top : BL;
    Bot : BL;
    Top_Bottom : forall a : BL, a ≤ Top /\ Bot ≤ a
  }.
Notation  top := (Top _).
Notation  bot := (Bot _).
Notation TB := (Top_Bottom _).

Structure booleanLattice := BooleanLattice
  {
    BooL :> boundedLattice;
    Distr: (@Distributive BooL);
    ExComplement : forall a : BooL, (exists b, (a ⊔ b = top ) /\ (a ⊓ b = bot) ) 
  }.
Notation Dist := (Distr _).
Notation ExComp := (ExComplement _).

Lemma ajBot {T : boundedLattice} (z : T) : forall a : T, a ⊔ bot = a.
Proof.
move=> a.
rewrite (L2 z) -(ConnectJ z).
by move: (TB a) => /proj2.
Qed.

Lemma amTop {T : boundedLattice} (z : T) : forall a : T, a ⊓ top = a.
Proof.
move=> a.
rewrite (L2d z) -(ConnectM z).
by move: (TB a) => /proj1.
Qed.

Definition Comp {T : boundedLattice} (a b : T ):= (a ⊔ b = top) /\ (a ⊓ b = bot).
 
Lemma compUnico {T : booleanLattice} (z : T) : forall a b c : T,
                (Comp a b /\ 
                Comp a c) -> b = c.
Proof.
move=> a b c.
rewrite /Comp. 
move=> [[H0 H1] [H2 H3]].
apply: antisym.
  rewrite (ConnectM z).
  rewrite -{2}(amTop z b).
  rewrite -H2.
  rewrite Dist.
  by rewrite [b ⊓ a](L2d z) H1 (L2 z) (ajBot z) (L2d z).
rewrite (ConnectM z).
rewrite -{2}(amTop z (c)).
rewrite -H0.
rewrite Dist.
by rewrite  [c ⊓ a](L2d z) H3 (L2 z) (ajBot z) (L2d z).
Qed.

Lemma lema4_15i {T : booleanLattice} (z : T) : (@Comp T top bot).
Proof.
split.
  move: (@Top_Bottom T top) => /proj2.
  by rewrite (ConnectJ z) (L2 z).
move: (@Top_Bottom T bot) => /proj1.
by rewrite (ConnectM z) (L2d z).
Qed.

Lemma lema4_15ii {T : booleanLattice} (z : T) : forall a b c : T, Comp a b -> Comp b c -> c = a.
Proof.
move=> a b c.
rewrite /Comp.
rewrite (L2 z) (L2d z).
move=> [H0 H1] [H2 H3].
apply: (compUnico z b).
rewrite /Comp.
by split.
Qed.
 
Lemma lema4_15iii {T : booleanLattice} (z : T) : forall a b caub ca cb canb : T, 
                                         (Comp (a ⊔ b) caub -> Comp a ca -> Comp b cb -> (caub = ca ⊓ cb))
                                         /\ (Comp (a ⊓ b) canb -> Comp a ca -> Comp b cb -> (canb = ca ⊔ cb)).
Proof.
move=> a b caub ca cb canb.
move: (Distr T).
rewrite /Distributive (Lema4_3 z) => Dis.
split.
  rewrite /Comp.
  move=> [H0 H1] [H2 H3] [H4 H5].
  apply: (compUnico z (a ⊔ b)).
  split.
    by [].
  split.
    rewrite Dis {1}[a ⊔ b](L2 z) (L1 z) H2.
    rewrite (L1 z) H4.
    move: (TB b) (TB a).
    move=> /proj1/(ConnectJ z)-bTop /proj1/(ConnectJ z)-aTop.
    by rewrite bTop aTop amTop.
  rewrite (L2d z) Dist (L2d z) -(L1d z) H3.
  rewrite (L1d z) [cb ⊓ b](L2d z) H5.
  move: (TB cb) (TB ca).
  move=> /proj2/(ConnectM z)-eBot /proj2/(ConnectM z)-dBot.
  by rewrite (L2d z) eBot dBot ajBot.
rewrite /Comp.
move=> [H0 H1] [H2 H3] [H4 H5].
apply: ((compUnico z) (a ⊓ b)).
split.
  by [].
split.
  rewrite (L2 z) Dis (L2 z) -(L1 z) H2 (L2 z).
  rewrite (L1 z) [cb ⊔ b](L2 z) H4.
  move: (TB cb) (TB ca).
  move=> /proj1/(ConnectJ z)-eTop /proj1/(ConnectJ z)-dTop.
  by rewrite eTop dTop amTop.
rewrite Dist [a ⊓ b](L2d z) (L1d z) H3 (L2d z).
rewrite [b ⊓ a](L2d z) (L1d z) H5 [a ⊓ bot](L2d z).
move: (TB b) (TB a).
move=> /proj2/(ConnectM z)-bBot /proj2/(ConnectM z)-aBot.
by rewrite (L2d z) bBot (L2d z) aBot ajBot.
Qed.
 
Lemma lema4_15v {T : booleanLattice} (z : T) : forall a b c : T, Comp b c -> a ⊓ c = bot <-> a ≤ b.
Proof.
move=> a b c.
move: (Distr T).
rewrite /Distributive (Lema4_3 z) => DistD.
move=> /dobl [CB [H0 H1]].
split.
  move=> H2.
  rewrite (ConnectM z).
  move: (amTop z a).
  by rewrite -H0 Dist H2 (ajBot z) (L2d z).
rewrite (ConnectJ z) => H.
move: (ExComp a).
case => a0 [aTop aBot].
have CA : Comp a a0.
  by [].
move: (TB c) => /proj2.
rewrite (ConnectM z) -{1}aBot (L2d z) (L1d z).
move: (lema4_15iii z a b c a0 c (a ⊓ b) ) => /proj1.
rewrite H.
move=> /(_ CB) /(_ CA) /(_ CB)-Compl.
by rewrite -Compl.
Qed.
