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


Structure ordtype (T : Type) := Ordtype { ord :> T -> T -> Prop;
                                          reflexT : reflexive ord;
                                          antisymT : antisymetric ord;
                                          transT : transitive ord  }.

Structure lattice {T : Type} (ord_T : ordtype T) := Lattice 
  { joinT : T -> T -> T;
    jHT : (forall z : T , forall x y : T,  (ord_T x z /\ ord_T y z) <-> ord_T ( joinT x y) z);
    meetT : T -> T -> T;
    mHT : (forall z : T , forall x y : T,  (ord_T z x /\ ord_T z y) <-> ord_T z ( meetT x y))
   }.


Section Propiedades_de_Lattices.

Variable T : Type.
Variable ord : ordtype T.
Notation "x ≤ y" := (ord x y) (at level 50).
Notation reflex := (reflexT T ord).
Notation antisym := (antisymT T ord).
Notation trans := (transT T ord).
Variable L : lattice ord.
Notation "x ⊓ y" := (@meetT T ord L x y) (at level 50).
Notation "x ⊔ y" := (@joinT T ord L x y) (at level 50).
Notation JH := (@jHT T ord L).
Notation MH := (@mHT T ord L).


Lemma ab_leq_jab : forall a b : T ,   a ≤ (a ⊔ b) /\  b ≤ (a ⊔ b).
Proof.
move=> a b.
split.
  by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj1.
by move: (reflex (a ⊔ b)); rewrite -(JH (a ⊔ b) a b) => /proj2.
Qed.

Lemma mab_leq_ab : forall a b : T ,  (a ⊓ b) ≤ a /\ (a ⊓ b) ≤ b.
Proof.
move=> a b.
split.
  by move: (reflex (a ⊓ b)); rewrite -(MH (a ⊓ b) a b) => /proj1.
by move: (reflex (a ⊓ b)); rewrite -(MH (a ⊓ b) a b) => /proj2.
Qed.


Lemma ConnectJ : forall a b : T ,  ord a b <-> (a ⊔ b = b).
Proof.
split.
move=> abLeq.
  apply: (antisym (a ⊔ b) b ).
    rewrite -(JH b a b).
    split.
      by [].
    by apply: (reflex b ).
  move: (reflex (a ⊔ b)).
  by rewrite -(JH (a ⊔ b) a b) => /proj2.
move=> H.
move: (reflex (a ⊔ b)).
rewrite {2}H.
move: (ab_leq_jab a b) => /proj1.
by apply: (trans a (a ⊔ b) b).
Qed.

Lemma ConnectM : forall a b : T ,  ord a b <-> (a ⊓ b = a).
Proof.
split.
move=> abLeq.
apply: (antisym (a ⊓ b) a ).
  move: (reflex (a ⊓ b)).
  by rewrite -(MH (a ⊓ b) a b) => /proj1.
rewrite -(MH a a b).
split.
  by apply: (reflex a).
by [].
move=> H.
move: (mab_leq_ab a b) => /proj2.
move: (reflex (a ⊓ b)).
rewrite {1}H.
by apply: (trans a (a ⊓ b) b).
Qed.

(* Propiedades L1 a L4*)

Lemma L3 : forall a : T , a ⊔ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /(ConnectJ a a).
Qed.

Lemma L3d : forall a : T , a ⊓ a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /(ConnectM a a).
Qed.


Lemma L2 : forall a b : T , a ⊔ b = b ⊔ a.
Proof.
move=> a b.
apply: (antisym (a ⊔ b)  (b ⊔ a)). (*Por Antisimetría*)
  move: (ab_leq_jab b a) => /and_comm.
  by rewrite (JH (b ⊔ a) a b). 
move: (ab_leq_jab a b) => /and_comm.
by rewrite (JH (a ⊔ b) b a).
Qed.



Lemma L2d : forall a b : T , a ⊓ b = b ⊓ a.
Proof.
move=> a b.
apply: (antisym (a ⊓ b)  (b ⊓ a)). (*Por Antisimetría*)
  move: (mab_leq_ab a b) => /and_comm.
  by rewrite (MH (a ⊓ b) b a). 
move: (mab_leq_ab b a) => /and_comm.
by rewrite (MH (b ⊓ a) a b).
Qed.


Lemma L4 : forall a b : T , a ⊔ (a ⊓ b) = a.
Proof.
move=> a b.
move: (mab_leq_ab a b) => /proj1. (*Vemos que inf a b ≤ a *)
move=> /(ConnectJ (a ⊓ b) a). (*Aplicamos el Connecting Lemma para ver que inf a b ∨ a = a*)
by rewrite L2.
Qed.

Lemma L4d : forall a b : T , a ⊓ (a ⊔ b) = a.
Proof.
move=> a b.
move: (ab_leq_jab a b) => /proj1. (*Vemos que a ≤ sup a b *)
by move=> /(ConnectM a (a ⊔ b) ). (*Aplicamos el Connecting Lemma para ver que sup a b ∧ a = a*)
Qed.

Lemma L1 : forall a b c : T , (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof. 
have c_leq_jab: forall x y z : T , ord z y -> ord z (x ⊔ y).
    move=>x y z z_leq_y; move: (ab_leq_jab x y) => /proj2; move: z_leq_y; by apply: (trans z y (x ⊔ y) ).
move=> a b c.
apply: (antisym ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(JH (a ⊔ (b ⊔ c)) (a ⊔ b) c).
  split.
    rewrite -(JH (a ⊔ (b ⊔ c)) a b).
    split.
      by move: (ab_leq_jab a (b ⊔ c)) => /proj1. (*1° caso a ≤ sup a (sup b c)*)
    by move: (ab_leq_jab b c) => /proj1 /(c_leq_jab a (b ⊔ c) b). (*2° caso b ≤ sup a (sup b c)*)
  by move: (ab_leq_jab b c) => /proj2 /(c_leq_jab a (b ⊔ c) c). (*c ≤ sup a (sup b c)*)
rewrite -(JH ((a ⊔ b) ⊔ c) a (b ⊔ c)).
split.
  rewrite (L2).
  move: (ab_leq_jab a b) => /proj1.
  by move=> /(c_leq_jab c (a ⊔ b) a).
rewrite -(JH ((a ⊔ b) ⊔ c ) b c).
split.
  move: (ab_leq_jab a b) => /proj2; rewrite [_ ⊔ c](L2).
  by move=> /(c_leq_jab c (a ⊔ b) b).  (*sup c (sup a b)*)
by move: (ab_leq_jab (a ⊔ b) c) => /proj2. (*c ≤ sup (sup a b) c*)
Qed.


Lemma L1d : forall a b c : T , (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof. 
have mab_leq_c: forall x y z : T , ord x z -> ord (x ⊓ y) z.
    move=>x y z H0; move: (mab_leq_ab x y) => /proj1-H1; move: H1 H0; by apply: (trans (x ⊓ y) x z ).
move=> a b c.
apply: (antisym ((a ⊓ b) ⊓ c) (a ⊓ (b ⊓ c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(MH ((a ⊓ b) ⊓ c) a (b ⊓ c) ).
  split.
    by move: (mab_leq_ab a b) => /proj1 /(mab_leq_c (a ⊓ b) c a). (*inf (inf a b) c ≤ a*)
  rewrite -(MH ((a ⊓ b) ⊓ c) b c ).
  split.
    by move: (mab_leq_ab a b) => /proj2 /(mab_leq_c (a ⊓ b) c b).  (*inf (inf a b) c ≤ b*)
  by move: (mab_leq_ab (a ⊓ b) c) => /proj2.
rewrite -(MH (a ⊓ (b ⊓ c)) (a ⊓ b) c ).
split.
  rewrite -(MH (a ⊓ (b ⊓ c)) a b ).
  split.
    by move: (mab_leq_ab a (b ⊓ c)) => /proj1.  (*inf a (inf b c) ≤ a*)
  move: (mab_leq_ab b c) => /proj1.
  by rewrite [a ⊓ _](L2d) => /(mab_leq_c (b ⊓ c) a b).  (*inf a (inf b c) ≤ b*)
move: (mab_leq_ab b c) => /proj2.
by rewrite [a ⊓ _](L2d) => /(mab_leq_c (b ⊓ c) a c).  (*inf a (inf b c) ≤ c*)
Qed.



Structure latticeAlg {T : Type} :=
                    LatticeAlg {
                     j : T -> T -> T;
                     m : T -> T -> T;
                     l1 : forall a b c : T, j (j a b) c = j a (j b c);
                     l1d : forall a b c : T, m (m a b) c = m a (m b c);
                     l2 : forall a b : T, j a b = j b a;
                     l2d : forall a b : T, m a b = m b a;
                     l3 : forall a : T, j a a = a;
                     l3d : forall a : T, m a a = a;
                     l4 : forall a b : T, j a (m a b) = a;
                     l4d : forall a b : T, m a (j a b) = a
                    }.

Canonical Alg_lattice := LatticeAlg T (@joinT T ord L) (@meetT T ord L) L1 L1d L2 L2d L3 L3d L4 L4d.

Section AlgtoSet.
Variable AlgL : @latticeAlg T.
Definition joinAlg := j AlgL.
Definition meetAlg := m AlgL.
Definition L1_Alg := l1 AlgL.
Definition L1d_Alg := l1d AlgL.
Definition L2_Alg := l2 AlgL.
Definition L2d_Alg := l2d AlgL.
Definition L3_Alg := l3 AlgL.
Definition L3d_Alg := l3d AlgL.
Definition L4_Alg := l4 AlgL.
Definition L4d_Alg := l4d AlgL.

Lemma AlgToSet1 : forall a b : T, (joinAlg a  b = b) <-> (meetAlg a b = a).
Proof.
split.
  move=> jab_b.
  have HL4d: meetAlg a (joinAlg a b ) = a.
    by apply: (L4d_Alg a b).
  by move: HL4d; rewrite jab_b.
move=> mab_a.
have HL4: joinAlg b (meetAlg a b) = b.
  rewrite /meetAlg (L2d_Alg). 
  by apply: (L4_Alg b a).
by move: HL4; rewrite mab_a /joinAlg (L2_Alg).
Qed.


Definition nord (a b : T) := joinAlg a b = b.
Check nord.

Lemma AlgToSetReflex : reflexive nord.
Proof.
  move=> a.
  rewrite /nord.
  by apply: (L3_Alg a).
Qed.

Lemma AlgToSetAntisym : antisymetric nord.
Proof.
  move=> a b. rewrite /nord /joinAlg => supb.
  rewrite (L2_Alg b a) => supa.
  by move: supb; rewrite supa.
Qed.


Lemma AlgToSetTrans : transitive nord.
Proof.
move=> a b c; rewrite /nord /joinAlg.
move=> supab supbc.
by move: (L1_Alg a b c); rewrite (supab) (supbc).
Qed.

Check Ordtype.
Check AlgToSetReflex.


(* 
  El Canonical T_ordtype es la instancia de que nord y sus prubas 
  son un elemento de ordtype, es decir, un orden.
*)


Canonical T_ordtype := Ordtype T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans.
Print T_ordtype.

Lemma AlgToSet_joinAlg: forall z : T, (forall x y : T, (nord x z /\ nord y z) <-> nord (joinAlg x y) z).
Proof.
move=> z x y.
split.
  move=> [H1 H2]; rewrite /nord.
  have supxz: joinAlg x z = z.
    by move: H1.
  have supyz: joinAlg y z = z.
    by move: H2.
  by move: supxz; rewrite -{1}(supyz) /joinAlg -(L1_Alg x y z).
move=> H1.
have cotaS: forall a b : T, (nord a (joinAlg a b)) /\ (nord b (joinAlg a b)).
  move=> a b.
  split.
    by rewrite /nord /joinAlg -(L1_Alg a a b) L3_Alg.
  by rewrite /nord /joinAlg (L2_Alg) (L1_Alg a b b) L3_Alg.
have trasnord: forall x y z :T, nord x y -> nord y z -> nord x z.
    by move: (AlgToSetTrans). 
split.
  move: (cotaS x y) H1 => /proj1.
  by apply: (trasnord x (joinAlg x y) z ).
move: H1; move: (cotaS x y); move=> /proj2.
by apply: (trasnord y (joinAlg x y) z ).
Qed.


Lemma AlgToSet_meetAlg: forall z : T, (forall x y : T, (nord z x /\ nord z y) <-> nord z (meetAlg x y) ).
Proof.
move=> z x y.
split.
  rewrite /nord; move=> [/(AlgToSet1)-H1 /(AlgToSet1)-H2]; rewrite AlgToSet1.
  by move: H1; rewrite -{1}(H2) /meetAlg (L1d_Alg z y x) (L2d_Alg y x).
move=> H1.
have cotaI: forall a b : T, (nord (meetAlg a b) a) /\ (nord (meetAlg a b) b).
  move=> a b.
  split.
    by rewrite /nord AlgToSet1 /meetAlg (L2d_Alg) -(L1d_Alg) L3d_Alg.
  by rewrite /nord AlgToSet1 /meetAlg (L1d_Alg) L3d_Alg.
have trasnord: forall x y z :T, nord x y -> nord y z -> nord x z.
  by move: AlgToSetTrans.
split.
  move: (cotaI x y) => /proj1; move: H1. 
  by apply: (trasnord z (meetAlg x y) x ).
move: (cotaI x y) => /proj2; move: H1.
by apply: (trasnord z (meetAlg x y) y ).
Qed.


(* 
  El Canonical T_lattice es la instancia de que lo que defino en LatticeAlg y sus prubas 
  son un elemento de lattice, es decir, una Lattice como se definió usando un orden.
*)

Canonical T_lattice := Lattice T (Ordtype T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans)
                       joinAlg AlgToSet_joinAlg meetAlg AlgToSet_meetAlg.

Print T_lattice.

Lemma join_eq : forall a b : T,  joinAlg a b = joinT T_ordtype T_lattice a b.
Proof. by []. Qed.

Lemma meet_eq : forall a b : T,  meetAlg a b = meetT T_ordtype T_lattice a b.
Proof. by []. Qed.


End AlgtoSet.
End Propiedades_de_Lattices.

Section Prop219.


Variables L K : Type.
Variable f : L -> K.
Variables (ord_L : ordtype L) (ord_K : ordtype K).
Notation reflex_L:= (reflexT L ord_L).
Notation reflex_K:= (reflexT K ord_K).
Notation antisym_L:= (antisymT L ord_L).
Notation antisym_K:= (antisymT K ord_K).
Notation trans_L:= (transT L ord_L).
Notation trans_K:= (transT K ord_K).
Variable Lattice_L : lattice ord_L.
Variable Lattice_K : lattice ord_K.
Notation join_L := (@joinT L ord_L Lattice_L).
Notation join_K := (@joinT K ord_K Lattice_K).
Notation meet_L := (@meetT L ord_L Lattice_L).
Notation meet_K := (@meetT K ord_K Lattice_K).
Notation JH_L := (@jHT L ord_L Lattice_L).
Notation JH_K := (@jHT K ord_K Lattice_K).
Notation MH_L := (@mHT L ord_L Lattice_L).
Notation MH_K := (@mHT K ord_K Lattice_K).


Definition ordPreserv := forall a b : L, ord_L a b -> ord_K (f a) (f b).

Definition ordEmmbed := forall a b : L, ord_L a b <-> ord_K (f a) (f b).

Definition Biyective := (forall a b : L, (f a) = (f b) <-> a = b) /\ (forall b : K, (exists a : L, b = f a )).

Definition ordIso := Biyective /\ ordEmmbed .

Definition joinOrdPreserv := forall x y : L, ord_K (join_K (f x) (f y)) (f ( join_L x y)) .

Definition meetOrdPreserv := forall x y : L, ord_K (f ( meet_L x y)) (meet_K (f x) (f y)) .

Definition joinPreserv := forall x y : L, (join_K (f x) (f y)) = (f ( join_L x y)) .

Definition meetPreserv := forall x y : L, (f ( meet_L x y)) = (meet_K (f x) (f y)) .

Definition latticeIso := joinPreserv /\ meetPreserv /\ Biyective.

Lemma prop219i1 : ordPreserv  <-> joinOrdPreserv.
Proof.
split.
  rewrite /ordPreserv => ordenP.
  rewrite /joinOrdPreserv => a b.
  have cotainf : ord_L a (join_L a b) /\ ord_L b (join_L a b).
    move: (reflex_L (join_L a b) ).
    by move=> /(JH_L (join_L a b) a b ).
  move: cotainf => [cota_a cota_b].
  move: cota_a => /(ordenP a (join_L a b))-cota_fa.
  move: cota_b => /(ordenP b (join_L a b))-cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (JH_K (f (join_L a b)) (f a) (f b) ).
rewrite /joinOrdPreserv => H.
rewrite /ordPreserv => a b /((ConnectJ ))-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab K ord_K Lattice_K (f a) (f b)) => /proj1.
by apply: (trans_K (f a) (join_K (f a) (f b)) (f b) ).
Qed.


Lemma prop219i2 : ordPreserv <-> meetOrdPreserv.
Proof.
split.
  rewrite /ordPreserv => ordenP.
  rewrite /meetOrdPreserv => a b.
  move: (mab_leq_ab L ord_L Lattice_L a b) => [cota_a cota_b].
  move: cota_a => /(ordenP (meet_L a b) a)-cota_fa.
  move: cota_b => /(ordenP (meet_L a b) b)-cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (MH_K (f (meet_L a b)) (f a) (f b) ).
rewrite /meetOrdPreserv => H.
rewrite /ordPreserv => a b /((ConnectM))-mab_L.
move: (mab_leq_ab K ord_K Lattice_K (f a) (f b)) => /proj2.
move: (H a b); rewrite mab_L.
by apply: (trans_K (f a) (meet_K (f a) (f b)) (f b) ).
Qed.

Lemma prop219i3 : ordIso <-> latticeIso.
Proof.
split.
  rewrite /ordIso /ordEmmbed /Biyective. move=> [[inj sob] H].
  rewrite /latticeIso. 
  split.
    rewrite /joinPreserv => x y; apply: (antisymT K ord_K ).
    move: (prop219i1); rewrite /ordPreserv /joinOrdPreserv => /proj1-H2.
    apply: H2 => c d.
    by move: (H c d) => /proj1.
    move: (sob (join_K (f x) (f y))) => [a Ha].
    move: (ab_leq_jab K ord_K Lattice_K (f x) (f y) ).
    rewrite Ha; move=> [/H-xleqa /H-yleqa].
    by rewrite -H -(JH_L a x y).
    split.
      rewrite /meetPreserv => x y; apply: (antisymT K ord_K ).
      move: (prop219i2); rewrite /ordPreserv /meetOrdPreserv => /proj1-H2.
      apply: H2 => c d;
      by move: (H c d) => /proj1.
      move: (sob (meet_K (f x) (f y))) => [a Ha].
      move: (mab_leq_ab K ord_K Lattice_K (f x) (f y) ).
      rewrite Ha; move=> [/H-aleqx /H-aleqy].
      by rewrite -H -(MH_L a x y).
    by [].
rewrite /latticeIso; move=> [Hjoin [Hmeet [inj sob]]].
rewrite /ordIso.
split.
  by [].
rewrite /ordEmmbed => a b.
split.
  by move=> /ConnectJ /(inj (join_L a b) b ); rewrite -(Hjoin a b) -ConnectJ.
by rewrite (ConnectJ K ord_K Lattice_K) Hjoin inj -(ConnectJ).
Qed.

End Prop219.


Section LatticesModularesDistributivasBooleanas.

Variable T : Type.
Variable ord : ordtype T.
Notation "x ≤ y" := (ord x y) (at level 50).
Notation reflex := (reflexT T ord).
Notation antisym := (antisymT T ord).
Notation trans := (transT T ord).
Variable L : lattice ord.
Notation "x ⊓ y" := (@meetT T ord L x y) (at level 50). (* \sqcap *)
Notation "x ⊔ y" := (@joinT T ord L x y) (at level 50). (* \sqcup *)
Notation JH := (@jHT T ord L).
Notation MH := (@mHT T ord L).


Lemma Lema4_1i : forall a b c : T, ((a ⊓ b) ⊔ (a ⊓ c)) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c.
rewrite -MH.
split.
  rewrite -JH.
  split.
    by move: (mab_leq_ab T ord L a b) => /proj1.
  by move: (mab_leq_ab T ord L a c) => /proj1.
rewrite -JH.
move: (ab_leq_jab T ord L b c) => [cota_b cota_c].
split.
  move: (mab_leq_ab T ord L a b) cota_b => /proj2.
  by apply: trans.
move: (mab_leq_ab T ord L a c) cota_c => /proj2.
by apply: trans.
Qed.

Lemma Lema4_1id : forall a b c : T, (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ (a ⊔ c)).
Proof.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    by move: (ab_leq_jab T ord L a b) => /proj1.
  by move: (ab_leq_jab T ord L a c) => /proj1.
rewrite -MH.
move: (mab_leq_ab T ord L b c) => [cota_b cota_c].
split.
  move: (ab_leq_jab T ord L a b) => /proj2; move: cota_b .
  by apply: trans.
move: (ab_leq_jab T ord L a c) => /proj2; move: cota_c.
by apply: trans.
Qed.

Lemma Lema4_1ii : forall a b c : T, c ≤ a -> ((a ⊓ b) ⊔ c) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c /(ConnectM T ord L); rewrite (L2d) => H.
by move: (Lema4_1i a b c); rewrite H.
Qed.

Lemma Lema4_1iid : forall a b c : T, a ≤ c -> (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ c).
Proof.
move=> a b c /(ConnectJ T ord L); rewrite (L2d) => H.
by move: (Lema4_1id a b c); rewrite L2d H.
Qed.

Lemma Lema4_1iii : forall a b c : T, ((a ⊓ b) ⊔ (b ⊓ c) ⊔ (c ⊓ a)) ≤ ((a ⊔ b) ⊓ (b ⊔ c) ⊓ (c ⊔ a)).
Proof.
have aux : forall a b c : T, (a ⊓ b) ≤ (c ⊔ a).
  move=> a b c; move: (ab_leq_jab T ord L c a)=> /proj2; move: (mab_leq_ab T ord L a b) => /proj1.
  by apply: trans.
move=> a b c.
rewrite -JH.
split.
  rewrite -MH.
  split.
    have H1 : b ≤ ((a ⊔ b) ⊓ (b ⊔ c)).
      rewrite -MH; split. by move: (ab_leq_jab T ord L a b) => /proj2.
      by move: (ab_leq_jab T ord L b c) => /proj1.
    have H2 : ((a ⊓ b) ⊔ (b ⊓ c)) ≤ b.
      rewrite -JH; split. by move: (mab_leq_ab T ord L a b) => /proj2.
      by move: (mab_leq_ab T ord L b c) => /proj1.
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

Lemma Lema4_2i : forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)) <->
                                   (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))).
Proof.
split.
  by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite (L2d T ord L a c) H.
by move=> H1 /dobl [/(ConnectM)-H] /H1; rewrite (L2d T ord L a c) H.
Qed.

Lemma Lema4_2ii : (forall a b c : T, c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c))) <->
                  (forall p q r : T, (p ⊓ (q ⊔ (p ⊓ r))) = ((p ⊓ q) ⊔ (p ⊓ r))).
Proof.
split.
  move=> H p q r.
  move: (mab_leq_ab T ord L p r) => /proj1.
  rewrite (Lema4_2i).
  by apply: H.
move=> H a b c /(ConnectM T ord L)-cleqa.
rewrite -{1}cleqa {1}(L2d T ord L c a). 
by apply: (H a b c).
Qed.

Lemma Lema4_3 : (forall a b c : T, (a ⊓ (b ⊔ c)) = (a ⊓ b) ⊔ (a ⊓ c)) <-> 
                (forall p q r : T, (p ⊔ (q ⊓ r)) = (p ⊔ q) ⊓ (p ⊔ r)).
Proof.
split.
  move=> H p q r.
  move: (H (p ⊔ q) p r).
  rewrite [(p ⊔ q) ⊓ p]L2d [p ⊓ (p ⊔ q)]L4d [(p ⊔ q) ⊓ r]L2d.
  rewrite (H r p q).
  by rewrite -(L1 T ord L p (r ⊓ p) (r ⊓ q)) [r ⊓ p]L2d [p ⊔ (p ⊓ r)]L4 [r ⊓ q]L2d.
move=> H a b c.
move: (H (a ⊓ b) a c).
rewrite [(a ⊓ b) ⊔ a]L2 [a ⊔ (a ⊓ b)]L4.
rewrite [(a ⊓ b) ⊔ c]L2 (H c a b).
by rewrite -(L1d T ord L a (c ⊔ a) (c ⊔ b)) [c ⊔ a]L2 [a ⊓ (a ⊔ c)]L4d [c ⊔ b]L2.
Qed.

Definition Distributive := forall a b c : T, (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c)).

Definition Modular := forall a b c : T, (c ≤ a -> (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ c)).


Structure booleanL := BooleanL
  { 
    Top : T;
    Bot : T;
    Dist : Distributive;
    TopBot : forall a : T, a ≤ Top /\ Bot ≤ a;
    compl : T -> T;
    Complement: forall a : T, (a ⊔ (compl a) = Top) /\ (a ⊓ (compl a) = Bot)
  }.

Variable BL : booleanL.
Notation  top := (Top BL).
Notation  bot := (Bot BL).
Notation c := (compl BL).

Lemma ajBot : forall a : T, a ⊔ bot = a.
Proof.
move=> a.
rewrite L2 -ConnectJ.
by move: (TopBot BL a) => /proj2.
Qed.

Lemma amTop : forall a : T, a ⊓ top = a.
Proof.
move=> a.
rewrite -ConnectM.
by move: (TopBot BL a) => /proj1.
Qed.

Lemma compUnico : forall a b : T,  (a ⊔ b = top) /\ (a ⊓ b = bot) -> (c a) = b.
Proof.
move=> a b [H1 H2].
apply: antisym.
  rewrite (ConnectM T ord L ) -(amTop (c a)).
  rewrite -{2}H1.
  rewrite (Dist BL (c a) a b).
  move: (Complement BL a)=> /proj2-H3.
  by rewrite (amTop (c a)) [c a ⊓ a]L2d H3 L2 ajBot.
rewrite (ConnectM T ord L ) -{2}(amTop (b)).
move: (Complement BL a)=> /proj1-H3.
rewrite -H3.
rewrite (Dist BL b a (c a)).
by rewrite [b ⊓ a]L2d H2 L2 ajBot.
Qed.


Lemma lema4_15i : c top = bot /\ c bot = top.
Proof.
split.
  apply: (compUnico top bot).
  split.
    move: (TopBot BL top)=> /proj2.
    by rewrite (ConnectJ T ord L) L2.
  move: (TopBot BL top)=> /proj2.
  by rewrite (ConnectM T ord L) L2d.
apply: (compUnico bot top).
split.
  move: (TopBot BL top)=> /proj2.
  by rewrite (ConnectJ T ord L) L2.
move: (TopBot BL top)=> /proj2.
by rewrite (ConnectM T ord L) L2d.
Qed.

Lemma lema4_15ii : forall a : T, c (c a) = a.
Proof.
move=> a.
apply: (compUnico (c a) a).
rewrite L2 L2d.
by apply: Complement.
Qed.

Lemma lema4_15iii : forall a b : T, (c (a ⊔ b) = (c a) ⊓ (c b))
                                    /\ ((c (a ⊓ b) = (c a) ⊔ (c b))).
Proof.
move=> a b.
move: (Complement BL a) => [H1a H2a].
move: (Complement BL b) => [H1b H2b].
move: (Dist BL).
rewrite /Distributive.
rewrite Lema4_3 => H.
move: (TopBot BL b) => /proj1.
move=> /(ConnectJ T ord L)-HbTop.
move: (TopBot BL a) => /proj1.
move=> /(ConnectJ T ord L)-HaTop.
move: (TopBot BL b) => /proj2.
move=> /(ConnectM T ord L)-HbBot.
move: (TopBot BL a) => /proj2.
move=> /(ConnectM T ord L)-HaBot.
move: (TopBot BL (c b)) => /proj2.
move=> /(ConnectM T ord L)-HcbBot.
move: (TopBot BL (c a)) => /proj2.
move=> /(ConnectM T ord L)-HcaBot.
move: (TopBot BL (c b)) => /proj1.
move=> /(ConnectJ T ord L)-HcbTop.
move: (TopBot BL (c a)) => /proj1.
move=> /(ConnectJ T ord L)-HcaTop.
split.
  apply: (compUnico (a ⊔ b) ((c a) ⊓ (c b))).
  split.
    rewrite (H (a ⊔ b) (c a) (c b)) L2 -L1 [c a ⊔ a]L2 H1a.
    rewrite L1 H1b.
    by rewrite HaTop L2 HbTop amTop.
  rewrite [(a ⊔ b) ⊓ (c a ⊓ c b)]L2d .
  rewrite (Dist BL (c a ⊓ c b) a b).
  rewrite [((c a ⊓ c b) ⊓ a)]L2d -L1d H2a L1d [c b ⊓ b]L2d H2b.
  by rewrite HcbBot L2d HcaBot ajBot.
apply: (compUnico (a ⊓ b) ((c a) ⊔ (c b))).
split.
  rewrite L2 H L2 L1 [c b ⊔ b]L2 H1b.
  by rewrite -L1 H1a L2 HcbTop HcaTop amTop.
rewrite (Dist BL) -L2d -L1d [c a ⊓ a]L2d H2a.
by rewrite L1d H2b HbBot L2d HaBot ajBot.
Qed.

Lemma lema4_15iv : forall a b : T, (c (c a ⊔ c b) = (a ⊓ b))
                                    /\ (c (c a ⊓ c b) = (a ⊔ b)).
Proof.
move=> a b.
move: (lema4_15iii (c a) (c b))=> [H1 H2].
split.
  by rewrite H1 lema4_15ii lema4_15ii.
by rewrite H2 lema4_15ii lema4_15ii.
Qed.

Lemma lema4_15v : forall a b : T, (a ⊓ (c b) = bot) <-> (a ≤ b).
Proof.
move=> a b.
move: (Dist BL).
rewrite /Distributive.
rewrite Lema4_3 => DistD.
split.
  move=> H.
  rewrite (ConnectM T ord L).
  move: (ab_leq_jab T ord L a b) => /proj1.
  rewrite (ConnectM T ord L) -{1}(L3d T ord L a).
  move: (TopBot BL (a ⊓ a)) => /proj2.
  rewrite (ConnectJ T ord L) L2 -H.  
  rewrite -(Dist BL) -{1}(L3 T ord L a) -DistD => H2.
  move: (TopBot BL (a ⊔ b)) => /proj1.
  rewrite (ConnectM T ord L).
  move: (Complement BL b) => /proj1-comp_b.
  rewrite -comp_b {1}[a ⊔ b]L2 -DistD => H3.
  rewrite -H2 -H3 L2 [b ⊔ (a ⊓ c b)]L2 -DistD.
  move: (TopBot BL (a ⊓ b)) => /proj2.
  rewrite (ConnectJ T ord L) => H4.
  by rewrite H H4.
rewrite (ConnectJ T ord L) => H.
move: (Complement BL a) => /proj2-H2.
move: (TopBot BL (c b)) => /proj2.
rewrite (ConnectM T ord L) -{1}H2 L1d.
move: (lema4_15iii a b) => /proj1-Compl.
by rewrite -Compl H.
Qed.









