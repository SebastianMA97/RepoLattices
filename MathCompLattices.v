From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


Lemma dobl (A : Prop) :  A <-> A /\ A.
Proof.
split. by [].
move=> [h1 h2]; by [].
Qed.


Section Lattices.
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
    mHT : (forall z : T , forall x y : T,  (z ≤ x /\ z ≤ y) <-> z ≤ ( meetT x y))
   }.

Notation "x ⊓ y" := (@meetT _ x y) (at level 50). (* \sqcap *)
Notation "x ⊔ y" := (@joinT _ x y) (at level 50). (* \sqcup *)
Notation reflex := (reflexT _).
Notation antisym := (antisymT _).
Notation trans := (transT _).
Notation JH := (@jHT _).
Notation MH := (@mHT _).

Lemma ab_leq_jab {T : lattice} : forall a b : T ,   a ≤ (a ⊔ b) /\  b ≤ (a ⊔ b).
Proof.
move=> a b.
split.
  by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj1.
by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj2.
Qed.

Lemma mab_leq_ab {T : lattice} : forall a b : T ,  (a ⊓ b) ≤ a /\ (a ⊓ b) ≤ b.
Proof.
move=> a b.
split.
  by move: (reflex (a ⊓ b)); rewrite -(MH (a ⊓ b) a b) => /proj1.
by move: (reflex (a ⊓ b)); rewrite -(MH (a ⊓ b) a b) => /proj2.
Qed.

Lemma ConnectJ {T : lattice} : forall a b : T ,  a ≤ b <-> (a ⊔ b = b).
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
move: (ab_leq_jab a b) => /proj1.
by apply: trans.
Qed.

Lemma ConnectM {T : lattice} : forall a b : T , a ≤ b <-> (a ⊓ b = a).
Proof.
split.
  move=> abLeq.
  apply: antisym.
    move: (reflex (a ⊓ b)).
    by rewrite -MH => /proj1.
  rewrite -MH.
  split.
    by apply: reflex a.
  by [].
move=> H.
move: (mab_leq_ab a b) => /proj2.
move: (reflex (a ⊓ b)).
rewrite {1}H.
by apply: trans.
Qed.

(* Propiedades L1 a L4*)

Lemma L3 {T : lattice} : forall a : T , a ⊔ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /ConnectJ.
Qed.

Lemma L3d {T : lattice} : forall a : T , a ⊓ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /ConnectM.
Qed.

Lemma L2 {T : lattice} : forall a b : T , a ⊔ b = b ⊔ a.
Proof.
move=> a b.
apply: antisym.
  move: (ab_leq_jab b a) => /and_comm.
  by rewrite JH. 
move: (ab_leq_jab a b) => /and_comm.
by rewrite JH.
Qed.

Lemma L2d {T : lattice} : forall a b : T , a ⊓ b = b ⊓ a.
Proof.
move=> a b.
apply: antisym.
  move: (mab_leq_ab a b) => /and_comm.
  by rewrite MH. 
move: (mab_leq_ab b a) => /and_comm.
by rewrite MH.
Qed.

Lemma L4 {T : lattice} : forall a b : T , a ⊔ (a ⊓ b) = a.
Proof.
move=> a b.
move: (mab_leq_ab a b) => /proj1.
move=> /ConnectJ.
by rewrite L2.
Qed.

Lemma L4d {T : lattice} : forall a b : T , a ⊓ (a ⊔ b) = a.
Proof.
move=> a b.
move: (ab_leq_jab a b) => /proj1.
by move=> /ConnectM.
Qed.

Lemma L1 {T : lattice} : forall a b c : T , (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof. 
have c_leq_jab: forall x y z : T , z ≤ y -> z ≤ (x ⊔ y).
    move=> x y z z_leq_y; move: (ab_leq_jab x y) => /proj2.
    move: z_leq_y; by apply: trans.
move=> a b c.
apply: antisym.
  rewrite -JH.
  split.
    rewrite -JH.
    split.
      by move: (ab_leq_jab a (b ⊔ c)) => /proj1. (*1° caso a ≤ sup a (sup b c)*)
    by move: (ab_leq_jab b c) => /proj1 /c_leq_jab. (*2° caso b ≤ sup a (sup b c)*)
  by move: (ab_leq_jab b c) => /proj2 /c_leq_jab. (*c ≤ sup a (sup b c)*)
rewrite -JH.
split.
  rewrite L2.
  move: (ab_leq_jab a b) => /proj1.
  by move=> /c_leq_jab.
rewrite -JH.
split.
  move: (ab_leq_jab a b) => /proj2; rewrite [_ ⊔ c](L2).
  by move=> /c_leq_jab.  (*sup c (sup a b)*)
by move: (ab_leq_jab (a ⊔ b) c) => /proj2. (*c ≤ sup (sup a b) c*)
Qed.

Lemma L1d {T : lattice} : forall a b c : T , (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. 
have mab_leq_c: forall x y z : T , x ≤ z -> (x ⊓ y) ≤ z.
    move=> x y z H0; move: (mab_leq_ab x y) => /proj1-H1.
    move: H1 H0; by apply: trans.
move=> a b c.
apply: antisym.
  rewrite -MH.
  split.
    by move: (mab_leq_ab a b) => /proj1 /mab_leq_c. (*inf (inf a b) c ≤ a*)
  rewrite -MH.
  split.
    by move: (mab_leq_ab a b) => /proj2 /mab_leq_c.  (*inf (inf a b) c ≤ b*)
  by move: (mab_leq_ab (a ⊓ b) c) => /proj2.
rewrite -MH.
split.
  rewrite -MH.
  split.
    by move: (mab_leq_ab a (b ⊓ c)) => /proj1.  (*inf a (inf b c) ≤ a*)
  move: (mab_leq_ab b c) => /proj1.
  by rewrite [a ⊓ _](L2d) => /mab_leq_c.  (*inf a (inf b c) ≤ b*)
move: (mab_leq_ab b c) => /proj2.
by rewrite [a ⊓ _](L2d) => /mab_leq_c.  (*inf a (inf b c) ≤ c*)
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

Check @joinT.

Canonical Alg_lattice {T : lattice} := LatticeAlg T (@joinT T) (@meetT T) L1 L1d L2 L2d L3 L3d L4 L4d.

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

Lemma prop219i1 {L K : lattice} {f : L -> K} : (@ordPreserv L K f)  <-> (@joinOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (ab_leq_jab a b) => [/(ordenP)-cota_fa /(ordenP)-cota_fb].
  rewrite -JH.
  by split.
rewrite /joinOrdPreserv => H.
move=> a b /ConnectJ-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab (f a) (f b)) => /proj1.
by apply: trans.
Qed.


Lemma prop219i2 {L K : lattice} {f : L -> K} : (@ordPreserv L K f) <-> (@meetOrdPreserv L K f).
Proof.
split.
  rewrite /ordPreserv => ordenP.
  move=> a b.
  move: (mab_leq_ab a b) => [/ordenP-cota_fa /ordenP-cota_fb].
  move: (conj cota_fa cota_fb).
  by rewrite MH.
rewrite /meetOrdPreserv => H.
move=> a b /((ConnectM))-mab_L.
move: (mab_leq_ab (f a) (f b)) => /proj2.
move: (H a b); rewrite mab_L.
by apply: trans.
Qed.

Lemma prop219i3 {L K : lattice} {f : L -> K} : (@ordIso L K f) <-> (@latticeIso L K f).
Proof.
split.
  rewrite /ordIso /ordEmmbed /Biyective; move=> [[inj sob] H].
  rewrite /latticeIso. 
  split.
    move=> x y; apply: antisym.
      move: (@prop219i1 L K f); rewrite /ordPreserv /joinOrdPreserv => /proj1-H2.
      apply: H2 => c d.
      by move: (H c d) => /proj1.
    move: (sob ((f x) ⊔ (f y))) => [a Ha].
    move: (ab_leq_jab (f x) (f y)).
    rewrite Ha; move=> [/H-xleqa /H-yleqa].
    by rewrite -H -JH.
  split.
    move=> x y; apply: antisym.
      move: (@prop219i2 L K f); rewrite /ordPreserv /meetOrdPreserv => /proj1-H2.
      apply: H2 => c d;
      by move: (H c d) => /proj1.
      move: (sob ((f x) ⊓ (f y))) => [a Ha].
      move: (mab_leq_ab (f x) (f y)).
      rewrite Ha; move=> [/H-aleqx /H-aleqy].
      by rewrite -H -MH.
    by [].
rewrite /latticeIso; move=> [Hjoin [Hmeet [inj sob]]].
split.
  by [].
move=> a b.
split.
  by move=> /ConnectJ /inj; rewrite -Hjoin -ConnectJ.
by rewrite ConnectJ Hjoin inj -(ConnectJ).
Qed.

(* Lattices modulares, distributivas y booleanas *)

Lemma Lema4_1i {T : lattice} : forall a b c : T, ((a ⊓ b) ⊔ (a ⊓ c)) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c.
rewrite -MH.
split.
  rewrite -JH.
  split.
    by move: (mab_leq_ab a b) => /proj1.
  by move: (mab_leq_ab a c) => /proj1.
rewrite -JH.
move: (ab_leq_jab b c) => [cota_b cota_c].
split.
  move: (mab_leq_ab a b) cota_b => /proj2.
  by apply: trans.
move: (mab_leq_ab a c) cota_c => /proj2.
by apply: trans.
Qed.

Lemma Lema4_1id {T : lattice} : forall a b c : T, (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ (a ⊔ c)).
Proof.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    by move: (ab_leq_jab a b) => /proj1.
  by move: (ab_leq_jab a c) => /proj1.
rewrite -MH.
move: (mab_leq_ab b c) => [cota_b cota_c].
split.
  move: (ab_leq_jab a b) => /proj2; move: cota_b .
  by apply: trans.
move: (ab_leq_jab a c) => /proj2; move: cota_c.
by apply: trans.
Qed.

Lemma Lema4_1ii {T : lattice} : forall a b c : T, c ≤ a -> ((a ⊓ b) ⊔ c) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c /ConnectM; rewrite L2d => H.
by move: (Lema4_1i a b c); rewrite H.
Qed.

Lemma Lema4_1iid {T : lattice} : forall a b c : T, a ≤ c -> (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ c).
Proof.
move=> a b c /ConnectJ; rewrite (L2d) => H.
by move: (Lema4_1id a b c); rewrite L2d H.
Qed.

Lemma Lema4_1iii {T : lattice} : forall a b c : T, ((a ⊓ b) ⊔ (b ⊓ c) ⊔ (c ⊓ a)) ≤ ((a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a)).
Proof.
have aux : forall a b c : T, (a ⊓ b) ≤ (c ⊔ a).
  move=> a b c; move: (ab_leq_jab c a)=> /proj2.
  move: (mab_leq_ab a b) => /proj1.
  by apply: trans.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    have H1 : b ≤ ((a ⊔ b) ⊓ (b ⊔ c)).
      rewrite -MH.
      split.
        by move: (ab_leq_jab a b) => /proj2.
      by move: (ab_leq_jab b c) => /proj1.
    have H2 : ((a ⊓ b) ⊔ (b ⊓ c)) ≤ b.
      rewrite -JH.
      split.
        by move: (mab_leq_ab a b) => /proj2.
      by move: (mab_leq_ab b c) => /proj1.
    by move: H1; move: H2; apply: trans.
  rewrite -JH.
  split.
    by apply: aux.
  by rewrite (L2d) (L2); apply aux.
rewrite -MH.
split.
  rewrite -MH.
  split.
    by rewrite (L2d) (L2); apply aux.
  by apply: aux.
by rewrite L2; apply: aux.
Qed.

Lemma Lema4_2i {T : lattice} : forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)) <->
                                   (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))).
Proof.
split.
  by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite (L2d a c) H.
by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite (L2d a c) H.
Qed.

Lemma Lema4_2ii {T : lattice} : (forall a b c : T, c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))) <->
                  (forall p q r : T, (p ⊓ (q ⊔ (p ⊓ r))) = ((p ⊓ q) ⊔ (p ⊓ r))).
Proof.
split.
  move=> H p q r.
  move: (mab_leq_ab p r) => /proj1.
  rewrite (Lema4_2i).
  by apply: H.
move=> H a b c /ConnectM-cleqa.
rewrite -{1}cleqa {1}(L2d c a). 
by apply: H.
Qed.

Lemma Lema4_3 {T : lattice} : (forall a b c : T, (a ⊓ (b ⊔ c)) = (a ⊓ b) ⊔ (a ⊓ c)) <-> 
                (forall p q r : T, (p ⊔ (q ⊓ r)) = (p ⊔ q) ⊓ (p ⊔ r)).
Proof.
split.
  move=> H p q r.
  move: (H (p ⊔ q) p r).
  rewrite [(p ⊔ q) ⊓ p]L2d [p ⊓ (p ⊔ q)]L4d [(p ⊔ q) ⊓ r]L2d.
  rewrite (H r p q).
  by rewrite -L1 [r ⊓ p]L2d [p ⊔ (p ⊓ r)]L4 [r ⊓ q]L2d.
move=> H a b c.
move: (H (a ⊓ b) a c).
rewrite [(a ⊓ b) ⊔ a]L2 [a ⊔ (a ⊓ b)]L4.
rewrite [(a ⊓ b) ⊔ c]L2 (H c a b).
by rewrite -L1d [c ⊔ a]L2 [a ⊓ (a ⊔ c)]L4d [c ⊔ b]L2.
Qed.

Definition Distributive {T : lattice} := forall a b c : T, (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c)).

Definition Modular {T : lattice} := forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)).

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

Lemma ajBot {T : boundedLattice} : forall a : T, a ⊔ bot = a.
Proof.
move=> a.
rewrite L2 -ConnectJ.
by move: (TB a) => /proj2.
Qed.

Lemma amTop {T : boundedLattice} : forall a : T, a ⊓ top = a.
Proof.
move=> a.
rewrite -ConnectM.
by move: (TB a) => /proj1.
Qed.

Definition Comp {T : booleanLattice} (a b : T ):= (a ⊔ b = top) /\ (a ⊓ b = bot).

Lemma compUnico {T : booleanLattice} : forall a b c : T,
                (Comp a b /\ 
                Comp a c) -> b = c.
Proof.
move=> a b c.
rewrite /Comp. 
move=> [[H0 H1] [H2 H3]].
apply: antisym.
  rewrite ConnectM.
  rewrite -{2}(amTop b).
  rewrite -H2.
  rewrite Dist.
  by rewrite [b ⊓ a]L2d H1 L2 ajBot.
rewrite ConnectM.
rewrite -{2}(amTop (c)).
rewrite -H0.
rewrite Dist.
by rewrite  [c ⊓ a]L2d H3 L2 ajBot.
Qed.

Lemma lema4_15i {T : booleanLattice} : (@Comp T top bot).
Proof.
split.
  move: (@Top_Bottom T top) => /proj2.
  by rewrite ConnectJ L2.
move: (@Top_Bottom T bot) => /proj1.
by rewrite ConnectM L2d.
Qed.

Lemma lema4_15ii {T : booleanLattice} : forall a b c : T, Comp a b -> Comp b c -> c = a.
Proof.
move=> a b c.
rewrite /Comp.
rewrite L2 L2d.
move=> [H0 H1] [H2 H3].
apply: (compUnico b).
rewrite /Comp.
by split.
Qed.

Lemma lema4_15iii {T : booleanLattice} : forall a b caub ca cb canb : T, (Comp (a ⊔ b) caub -> Comp a ca -> Comp b cb -> (caub = ca ⊓ cb))
                                    /\ (Comp (a ⊓ b) canb -> Comp a ca -> Comp b cb -> (canb = ca ⊔ cb)).
Proof.
move=> a b caub ca cb canb.
move: (Distr T).
rewrite /Distributive Lema4_3 => Dis.
split.
  rewrite /Comp.
  move=> [H0 H1] [H2 H3] [H4 H5].
  apply: (compUnico (a ⊔ b)).
  split.
    by [].
  split.
    rewrite Dis [a ⊔ b]L2 L1 H2.
    rewrite [b ⊔ a]L2 L1 H4.
    move: (TB b) (TB a).
    move=> /proj1/ConnectJ-bTop /proj1/ConnectJ-aTop.
    by rewrite bTop aTop amTop.
  rewrite L2d Dist L2d -L1d H3.
  rewrite L1d [cb ⊓ b]L2d H5.
  move: (TB cb) (TB ca).
  move=> /proj2/ConnectM-eBot /proj2/ConnectM-dBot.
  by rewrite eBot L2d dBot ajBot.
rewrite /Comp.
move=> [H0 H1] [H2 H3] [H4 H5].
apply: (compUnico (a ⊓ b)).
split.
  by [].
split.
  rewrite L2 Dis L2 -L1 H2 L2.
  rewrite L1 [cb ⊔ b]L2 H4.
  move: (TB cb) (TB ca).
  move=> /proj1/ConnectJ-eTop /proj1/ConnectJ-dTop.
  by rewrite eTop dTop amTop.
rewrite Dist [a ⊓ b]L2d L1d H3 L2d.
rewrite [b ⊓ a]L2d L1d H5 [a ⊓ bot]L2d.
move: (TB b) (TB a).
move=> /proj2/ConnectM-bBot /proj2/ConnectM-aBot.
by rewrite bBot aBot ajBot.
Qed.

Lemma lema4_15v {T : booleanLattice} : forall a b c : T, Comp b c -> a ⊓ c = bot <-> a ≤ b.
Proof.
move=> a b c.
move: (Distr T).
rewrite /Distributive Lema4_3 => DistD.
move=> /dobl [CB [H0 H1]].
split.
  move=> H2.
  rewrite ConnectM.
  move: (ab_leq_jab a b) => /proj1.
  rewrite ConnectM -{1}(L3d a).
  move: (TB (a ⊓ a)) => /proj2.
  rewrite ConnectJ L2 -H2.
  rewrite -Dist -{1}(L3 a) -DistD => H3.
  move: (TB (a ⊔ b)) => /proj1.
  rewrite ConnectM.
  rewrite -H0 {1}[a ⊔ b]L2 -DistD => H4.
  rewrite -H3 -H4 L2 [b ⊔ (a ⊓ c)]L2 -DistD.
  move: (TB (a ⊓ b)) => /proj2.
  rewrite ConnectJ => H5.
  by rewrite H2 H5.
rewrite ConnectJ => H.
move: (ExComp a).
case => a0 [aTop aBot].
have CA : Comp a a0.
  by [].
move: (TB c) => /proj2.
rewrite ConnectM -{1}aBot L1d.
move: (lema4_15iii a b c a0 c (a ⊓ b) ) => /proj1.
rewrite H.
move=> /(_ CB) /(_ CA) /(_ CB)-Compl.
by rewrite -Compl.
Qed.


(* Aquí empiezo a implementar del libro de Curry por el momento *)


Theorem Curry4_7 {T : lattice} : (forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ c)) 
                                 <-> (@Distributive T).
Proof.
split; last first.
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

Theorem Curry4_8 {T : lattice} : (forall a b c : T, (a ⊓ b ≤ c /\ a ≤ (b ⊔ c)) -> (a ≤ c))
                                 <-> (@Distributive T).
Proof.
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


