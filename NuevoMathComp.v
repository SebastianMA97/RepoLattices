From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


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
Notation reflex := (reflexT T ord).
Notation antisym := (antisymT T ord).
Notation trans := (transT T ord).
Variable L : lattice ord.
Notation join := (@joinT T ord L).
Notation meet := (@meetT T ord L).
Notation JH := (@jHT T ord L).
Notation MH := (@mHT T ord L).


Lemma ab_leq_jab : forall a b : T ,  ord a (join a b) /\ ord b (join a b) .
Proof.
move=> a b.
split.
  by move: (reflex (join a b)); rewrite -(JH (join a b) a b); move=> /proj1.
by move: (reflex (join a b)); rewrite -(JH (join a b) a b); move=> /proj2.
Qed.

Lemma mab_leq_ab : forall a b : T ,  ord (meet a b) a /\ ord (meet a b) b.
Proof.
move=> a b.
split.
  by move: (reflex (meet a b)); rewrite -(MH (meet a b) a b); move=> /proj1.
by move: (reflex (meet a b)); rewrite -(MH (meet a b) a b); move=> /proj2.
Qed.


Lemma ConnectJ : forall a b : T ,  ord a b <-> (join a b = b).
Proof.
split.
move=> abLeq.
  apply: (antisym (join a b) b ).
    rewrite -(JH b a b).
    split.
      by [].
    by apply: (reflex b ).
  move: (reflex (join a b)).
  by rewrite -(JH (join a b) a b); move=> /proj2.
move=> H.
move: (reflex (join a b)).
rewrite {2}H.
move: (ab_leq_jab a b); move=> /proj1.
by apply: (trans a (join a b) b).
Qed.

Lemma ConnectM : forall a b : T ,  ord a b <-> (meet a b = a).
Proof.
split.
move=> abLeq.
apply: (antisym (meet a b) a ).
  move: (reflex (meet a b)).
  by rewrite -(MH (meet a b) a b); move=> /proj1.
rewrite -(MH a a b).
split.
  by apply: (reflex a).
by [].
move=> H.
move: (mab_leq_ab a b); move=> /proj2.
move: (reflex (meet a b)).
rewrite {1}H.
by apply: (trans a (meet a b) b).
Qed.

(* Propiedades L1 a L4*)

Lemma L3 : forall a : T , join a a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /(ConnectJ a a).
Qed.

Lemma L3d : forall a : T , meet a a = a.
Proof.
move=> a.
move: (reflex  a). 
by move=> /(ConnectM a a).
Qed.


Lemma L2 : forall a b : T , join a b = join b a.
Proof.
move=> a b.
apply: (antisym (join a b)  (join b a)). (*Por Antisimetría*)
  move: (ab_leq_jab b a); move=> /and_comm.
  by rewrite (JH (join b a) a b). 
move: (ab_leq_jab a b); move=> /and_comm.
by rewrite (JH (join a b) b a).
Qed.



Lemma L2d : forall a b : T , meet a b = meet b a.
Proof.
move=> a b.
apply: (antisym (meet a b)  (meet b a)). (*Por Antisimetría*)
  move: (mab_leq_ab a b); move=> /and_comm.
  by rewrite (MH (meet a b) b a). 
move: (mab_leq_ab b a); move=> /and_comm.
by rewrite (MH (meet b a) a b).
Qed.


Lemma L4 : forall a b : T , join a (meet a b) = a.
Proof.
move=> a b.
move: (mab_leq_ab a b); move=> /proj1. (*Vemos que inf a b ≤ a *)
move=> /(ConnectJ (meet a b) a). (*Aplicamos el Connecting Lemma para ver que inf a b ∨ a = a*)
by rewrite L2.
Qed.

Lemma L4d : forall a b : T , meet a (join a b) = a.
Proof.
move=> a b.
move: (ab_leq_jab a b); move=> /proj1. (*Vemos que a ≤ sup a b *)
by move=> /(ConnectM a (join a b) ). (*Aplicamos el Connecting Lemma para ver que sup a b ∧ a = a*)
Qed.

Lemma L1 : forall a b c : T , join (join a b) c = join a (join b c).
Proof. 
have c_leq_jab: forall x y z : T , ord z y -> ord z (join x y).
    move=>x y z z_leq_y; move: (ab_leq_jab x y); move=> /proj2; move: z_leq_y; by apply: (trans z y (join x y) ).
move=> a b c.
apply: (antisym (join (join a b) c) (join a (join b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(JH (join a (join b c)) (join a b) c).
  split.
    rewrite -(JH (join a (join b c)) a b).
    split.
      move: (ab_leq_jab a (join b c)); by move=> /proj1. (*1° caso a ≤ sup a (sup b c)*)
    move: (ab_leq_jab b c); move=> /proj1; by move=> /(c_leq_jab a (join b c) b). (*2° caso b ≤ sup a (sup b c)*)
  move: (ab_leq_jab b c); move=> /proj2; by move=> /(c_leq_jab a (join b c) c). (*c ≤ sup a (sup b c)*)
rewrite -(JH (join (join a b) c) a (join b c)).
split.
  rewrite (L2).
  move: (ab_leq_jab a b); move=> /proj1.
  by move=> /(c_leq_jab c (join a b) a).
rewrite -(JH (join (join a b) c ) b c).
split.
  move: (ab_leq_jab a b); move=> /proj2. rewrite [join _ c](L2).
  by move=> /(c_leq_jab c (join a b) b).  (*sup c (sup a b)*)
move: (ab_leq_jab (join a b) c); by move=> /proj2. (*c ≤ sup (sup a b) c*)
Qed.


Lemma L1d : forall a b c : T , meet (meet a b) c = meet a (meet b c).
Proof. 
have mab_leq_c: forall x y z : T , ord x z -> ord (meet x y) z.
    move=>x y z H0; move: (mab_leq_ab x y); move=> /proj1-H1; move: H1 H0; by apply: (trans (meet x y) x z ).
move=> a b c.
apply: (antisym (meet (meet a b) c) (meet a (meet b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(MH (meet (meet a b) c) a (meet b c) ).
  split.
    move: (mab_leq_ab a b); move=> /proj1; by move=> /(mab_leq_c (meet a b) c a). (*inf (inf a b) c ≤ a*)
  rewrite -(MH (meet (meet a b) c) b c ).
  split.
    move: (mab_leq_ab a b); move=> /proj2; by move=> /(mab_leq_c (meet a b) c b).  (*inf (inf a b) c ≤ b*)
  move: (mab_leq_ab (meet a b) c); by move=> /proj2.
rewrite -(MH (meet a (meet b c)) (meet a b) c ).
split.
  rewrite -(MH (meet a (meet b c)) a b ).
  split.
    move: (mab_leq_ab a (meet b c)); by move=> /proj1.  (*inf a (inf b c) ≤ a*)
  move: (mab_leq_ab b c); move=> /proj1; rewrite [meet a _](L2d); by move=> /(mab_leq_c (meet b c) a b).  (*inf a (inf b c) ≤ b*)
move: (mab_leq_ab b c); move=> /proj2; rewrite [meet a _](L2d); by move=> /(mab_leq_c (meet b c) a c).  (*inf a (inf b c) ≤ c*)
Qed.



Structure latticeAlg {T : Type} :=
                    LatticeAlg {
                     j : T -> T -> T;
                     m : T -> T -> T;
                     l1 : forall a b c : T, j (j a b) c = j a (j b c);
                     l1d : forall a b c : T, m (m a b) c = m a (m b c);
                     l2 : forall a b : T, j a b = j b a;
                     l2d : forall a b : T, m a b = m b a;
                     l3 : forall a b : T, j a a = a;
                     l3d : forall a b : T, m a a = a;
                     l4 : forall a b : T, j a (m a b) = a;
                     l4d : forall a b : T, m a (j a b) = a
                    }.

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
   unfold meetAlg.
   rewrite (L2d_Alg). apply: (L4_Alg b a).
by move: HL4; rewrite mab_a; unfold joinAlg; rewrite (L2_Alg).
Qed.


Definition nord (a b : T) := joinAlg a b = b.


Lemma AlgToSetReflex : reflexive nord.
Proof.
  move=> a.
  unfold nord.
  by apply: (L3_Alg a).
Qed.

Lemma AlgToSetAntisym : antisymetric nord.
Proof.
  move=> a b. unfold nord; unfold joinAlg; move=> supb; rewrite (L2_Alg b a); move=> supa.
  by move: supb; rewrite supa.
Qed.


Lemma AlgToSetTrans : transitive nord.
Proof.
move=> a b c; unfold nord; unfold joinAlg.
move=> supab supbc.
by move: (L1_Alg a b c); rewrite (supab); rewrite (supbc).
Qed.

Check Ordtype.
Check AlgToSetReflex.


(* 
  El Canonical T_ordtype es la instancia de que nord y sus prubas 
  son un elemento de ordtype, es decir, un orden.
*)


Canonical T_ordtype := Ordtype T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans.

Lemma AlgToSet_joinAlg: forall z : T, (forall x y : T, (nord x z /\ nord y z) <-> nord (joinAlg x y) z).
Proof.
move=> z x y.
split.
  move=> [H1 H2]; unfold nord.
  have supxz: joinAlg x z = z.
    by move: H1.
  have supyz: joinAlg y z = z.
    by move: H2.
  by move: supxz; rewrite -{1}(supyz); unfold joinAlg; rewrite -(L1_Alg x y z).
move=> H1.
have cotaS: forall a b : T, (nord a (joinAlg a b)) /\ (nord b (joinAlg a b)).
  move=> a b.
  split.
    by unfold nord; unfold joinAlg; rewrite -(L1_Alg a a b); rewrite L3_Alg.
  by unfold nord; unfold joinAlg; rewrite (L2_Alg); rewrite (L1_Alg a b b); rewrite L3_Alg.
have trasnord: forall x y z :T, nord x y -> nord y z -> nord x z.
    by move: (AlgToSetTrans). 
split.
  move: H1; move: (cotaS x y); move=> /proj1.
  by apply: (trasnord x (joinAlg x y) z ).
move: H1; move: (cotaS x y); move=> /proj2.
by apply: (trasnord y (joinAlg x y) z ).
Qed.


Lemma AlgToSet_meetAlg: forall z : T, (forall x y : T, (nord z x /\ nord z y) <-> nord z (meetAlg x y) ).
Proof.
move=> z x y.
split.
  unfold nord; move=> [/(AlgToSet1)-H1 /(AlgToSet1)-H2]; rewrite AlgToSet1.
  by move: H1; rewrite -{1}(H2); unfold meetAlg; rewrite (L1d_Alg z y x); rewrite (L2d_Alg y x).
move=> H1.
have cotaI: forall a b : T, (nord (meetAlg a b) a) /\ (nord (meetAlg a b) b).
move=> a b.
split.
  by unfold nord; rewrite AlgToSet1; unfold meetAlg; rewrite (L2d_Alg); rewrite -(L1d_Alg); rewrite L3d_Alg.
by unfold nord; rewrite AlgToSet1; unfold meetAlg; rewrite (L1d_Alg); rewrite L3d_Alg.
have trasnord: forall x y z :T, nord x y -> nord y z -> nord x z.
    by move: AlgToSetTrans.
split.
  move: (cotaI x y); move=> /proj1; move: H1. 
  by apply: (trasnord z (meetAlg x y) x ).
move: (cotaI x y); move=> /proj2; move: H1.
by apply: (trasnord z (meetAlg x y) y ).
Qed.


(* 
  El Canonical T_lattice es la instancia de que lo que defino en LatticeAlg y sus prubas 
  son un elemento de lattice, es decir, una Lattice como se definió usando un orden.
*)

Canonical T_lattice := Lattice T (Ordtype T nord AlgToSetReflex AlgToSetAntisym AlgToSetTrans)
                       joinAlg AlgToSet_joinAlg meetAlg AlgToSet_meetAlg.



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


Definition joinPreserv := forall x y : L, ord_K (join_K (f x) (f y)) (f ( join_L x y)) .


Definition meetPreserv := forall x y : L, ord_K (f ( meet_L x y)) (meet_K (f x) (f y)) .

Lemma prop219i1 : ordPreserv  <-> joinPreserv.
Proof.
split.
  unfold ordPreserv; move=> ordenP.
  unfold joinPreserv; move=> a b.
  have cotainf : ord_L a (join_L a b) /\ ord_L b (join_L a b).
    move: (reflex_L (join_L a b) ).
    by move=> /(JH_L (join_L a b) a b ).
  move: cotainf; move=> [cota_a cota_b].
  move: cota_a; move=> /(ordenP a (join_L a b)) cota_fa.
  move: cota_b; move=> /(ordenP b (join_L a b)) cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (JH_K (f (join_L a b)) (f a) (f b) ).
unfold joinPreserv; move=> H.
unfold ordPreserv; move=> a b /((ConnectJ L ord_L Lattice_L a b))-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab K ord_K Lattice_K (f a) (f b)); move=> /proj1.
by apply: (trans_K (f a) (join_K (f a) (f b)) (f b) ).
Qed.


Lemma prop219i2 : ordPreserv <-> meetPreserv.
Proof.
split.
  unfold ordPreserv; move=> ordenP.
  unfold meetPreserv; move=> a b.
  move: (mab_leq_ab L ord_L Lattice_L a b); move=> [cota_a cota_b].
  move: cota_a; move=> /(ordenP (meet_L a b) a) cota_fa.
  move: cota_b; move=> /(ordenP (meet_L a b) b) cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (MH_K (f (meet_L a b)) (f a) (f b) ).
unfold meetPreserv; move=> H.
unfold ordPreserv; move=> a b /((ConnectM L ord_L Lattice_L a b))-mab_L.
move: (mab_leq_ab K ord_K Lattice_K (f a) (f b)); move=> /proj2.
move: (H a b); rewrite mab_L.
by apply: (trans_K (f a) (meet_K (f a) (f b)) (f b) ).
Qed.











