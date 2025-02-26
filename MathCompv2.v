From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


Variable L : Type.
Variable x y z : L.
Variable ord : L -> L -> Prop.
Notation "x ≤ y" := (ord x y) (at level 50). (*\leq + shift espacio*)
Hypothesis ReflexiveOrd : forall x : L , x ≤ x. 
Hypothesis AntisymetricOrd : forall x y : L , x ≤ y -> y ≤ x -> x = y.
Hypothesis TransitiveOrd : forall x y z : L , x ≤ y -> y ≤ z -> x ≤ z.
Variable sup inf : L -> L -> L.
Hypothesis LatticeSup : (forall z : L , forall x y : L,  (x ≤ z /\ y ≤ z) <-> sup x y ≤ z).
Hypothesis LatticeInf : (forall z : L , forall x y : L , (z ≤ x /\ z ≤ y) <-> z ≤ inf x y).
Variable join meet : L -> L -> L.
Notation "x ∨ y" := (join x y) (at level 50). (*\vee + shift espacio*)
Notation "x ∧ y" := (meet x y) (at level 50). (*\wedge + shift espacio*)
Hypothesis Ls : forall x y : L, sup x y = x ∨ y.
Hypothesis Li : forall x y : L, inf x y = x ∧ y.


Lemma AdjConnecting : forall a b : L ,  (a ≤ b) -> ((a ∨ b) = b) /\ ((a ∧ b) = a).
Proof.
move=> a b abLeq.
 split.
    rewrite -Ls. (*Empezamos con el supremo*)
    apply: (AntisymetricOrd (sup a b) b ).
      rewrite -((LatticeSup b) a b).
      split.
      by [].
      by apply: ReflexiveOrd b.
    have true_sup : sup a b ≤ sup a b.
      by apply: ReflexiveOrd (sup a b).
    move: true_sup.
    apply (LatticeSup (sup a b) a b).
  rewrite -Li. (*Seguimos con el infimo*)
  apply: (AntisymetricOrd (inf a b) a ).
    have true_inf : inf a b ≤ inf a b.
      by apply: ReflexiveOrd (inf a b).
    move: true_inf.
    apply (LatticeInf (inf a b) a b).
  rewrite -((LatticeInf a) a b).
  split.
    by apply: ReflexiveOrd a.
      by [].
Qed.

Lemma Connecting : forall a b : L , (a ≤ b <-> (a ∨ b) = b) /\  (a ≤ b <-> (a ∧ b) = a).
Proof.
split.
  split.
    move=> /AdjConnecting-SupInf.
    by destruct SupInf.
  rewrite -(Ls a b).
  move=> SupEq_b.
  move: (ReflexiveOrd b).
  rewrite -{1}SupEq_b.
  rewrite -(LatticeSup b a b).
  move=> H; by destruct H.
split.
  move=> /AdjConnecting-SupInf.
  by destruct SupInf.
rewrite -(Li a b).
  move=> InfEq_a.
  move: (ReflexiveOrd a).
  rewrite -{2}InfEq_a.
  rewrite -(LatticeInf a a b).
  move=> H; by destruct H.
Qed.

Lemma ab_leq_supab : forall a b : L , (a ≤ sup a b) /\ (b ≤ sup a b).
Proof.
move=> a b.
by move: (ReflexiveOrd (sup a b)); rewrite -(LatticeSup (sup a b) a b).
Qed.

Lemma infab_leq_ab : forall a b : L , (inf a b ≤ a) /\ (inf a b ≤ b).
Proof.
move=> a b.
by move: (ReflexiveOrd (inf a b)); rewrite -(LatticeInf (inf a b) a b).
Qed.

Lemma supComm: forall a b : L , sup a b = sup b a.
Proof.
move=> a b.
apply: (AntisymetricOrd (sup a b)  (sup b a)). (*Por Antisimetría*)
  move: (ab_leq_supab b a); move=> /and_comm; by rewrite (LatticeSup (sup b a) a b). 
move: (ab_leq_supab a b); move=> /and_comm. by rewrite (LatticeSup (sup a b) b a).
Qed.

Lemma infComm: forall a b : L , inf a b = inf b a.
Proof.
move=> a b.
apply: (AntisymetricOrd (inf a b)  (inf b a)). (*Por Antisimetría*)
  move: (infab_leq_ab a b); move=> /and_comm; by rewrite (LatticeInf (inf a b) b a). (*inf a b ≤ inf b a*) 
move: (infab_leq_ab b a); move=> /and_comm; by rewrite (LatticeInf (inf b a) a b).  (*inf b a ≤ inf a b*)
Qed.

(*Aquí empiezan los L1 hasta L4*)


Lemma L3: forall a : L , a ∨ a = a.
Proof.
move=> a.
move: (ReflexiveOrd a); by move=> /(AdjConnecting a a) /proj1.
Qed.

Lemma L3d: forall a : L , a ∧ a = a.
Proof.
move=> a.
move: (ReflexiveOrd a); by move=> /(AdjConnecting a a) /proj2.
Qed.


Lemma L2: forall a b : L , a ∨ b = b ∨ a.
Proof.
move=> a b.
rewrite -!Ls.
by apply: (supComm a b).
Qed.



Lemma L2d: forall a b : L , a ∧ b = b ∧ a.
Proof.
move=> a b.
rewrite -!Li.
by apply: (infComm a b).
Qed.


Lemma L4: forall a b : L , a ∨(a ∧ b) = a.
Proof.
move=> a b.
move: (infab_leq_ab a b); move=> /proj1. (*Vemos que inf a b ≤ a *)
move=> /(AdjConnecting (inf a b) a). (*Aplicamos el Lemma adjunto al Connecting Lemma para ver que inf a b ∨ a = a*)
rewrite !Li; move=> /proj1.
by rewrite L2.
Qed.

Lemma L4d: forall a b : L , a ∧ (a ∨ b) = a.
Proof.
move=> a b.
move: (ab_leq_supab a b); move=> /proj1. (*Vemos que a ≤ sup a b *)
move=> /(AdjConnecting a (sup a b) ) /proj2. (*Aplicamos el AdjConnecting Lemma para ver que sup a b ∧ a = a*)
by rewrite Ls.
Qed.

Lemma L1: forall a b c : L , (a ∨ b) ∨ c = a ∨ (b ∨ c).
Proof. 
have c_leq_supab: forall x y z : L , z ≤ y -> z ≤ sup x y.
    move=>x y z H0; move: (ab_leq_supab x y); move=> H1; destruct H1; by apply: (TransitiveOrd z y (sup x y) ).
move=> a b c.
rewrite -!Ls; apply: (AntisymetricOrd (sup (sup a b) c) (sup a (sup b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(LatticeSup (sup a (sup b c)) (sup a b) c).
  split.
    rewrite -(LatticeSup (sup a (sup b c)) a b).
    split.
      move: (ab_leq_supab a (sup b c)); by move=> /proj1. (*1° caso a ≤ sup a (sup b c)*)
    move: (ab_leq_supab b c); move=> /proj1; by move=> /(c_leq_supab a (sup b c) b). (*2° caso b ≤ sup a (sup b c)*)
  move: (ab_leq_supab b c); move=> /proj2; by move=> /(c_leq_supab a (sup b c) c). (*c ≤ sup a (sup b c)*)
rewrite -(LatticeSup (sup (sup a b) c) a (sup b c)).
split.
  move: (ab_leq_supab a b); move=> /proj1; rewrite supComm; rewrite [sup _ c]supComm.
  by move=> /(c_leq_supab c (sup b a)  a). (*a ≤ sup (sup a b) c*)
rewrite -(LatticeSup (sup (sup a b) c ) b c).
split.
  move: (ab_leq_supab a b); move=> /proj2; rewrite [sup _ c]supComm.
  by move=> /(c_leq_supab c (sup a b) b).  (*sup c (sup a b)*)
move: (ab_leq_supab (sup a b) c); by move=> /proj2. (*c ≤ sup (sup a b) c*)
Qed.


Lemma L1d: forall a b c : L , (a ∧ b) ∧ c = a ∧ (b ∧ c).
Proof. 
have infab_leq_c: forall x y z : L , x ≤ z -> inf x y ≤ z.
    move=>x y z H0; move: (infab_leq_ab x y); move=> /proj1-H1; move: H1 H0; by apply: (TransitiveOrd (inf x y) x z ).
move=> a b c.
rewrite -!Li; apply: (AntisymetricOrd (inf (inf a b) c) (inf a (inf b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(LatticeInf (inf (inf a b) c) a (inf b c) ).
  split.
    move: (infab_leq_ab a b); move=> /proj1; by move=> /(infab_leq_c (inf a b) c a). (*inf (inf a b) c ≤ a*)
  rewrite -(LatticeInf (inf (inf a b) c) b c ).
  split.
    move: (infab_leq_ab a b); move=> /proj2; by move=> /(infab_leq_c (inf a b) c b).  (*inf (inf a b) c ≤ b*)
  move: (infab_leq_ab (inf a b) c); by move=> /proj2.
rewrite -(LatticeInf (inf a (inf b c)) (inf a b) c ).
split.
  rewrite -(LatticeInf (inf a (inf b c)) a b ).
  split.
    move: (infab_leq_ab a (inf b c)); by move=> /proj1.  (*inf a (inf b c) ≤ a*)
  move: (infab_leq_ab b c); move=> /proj1; rewrite [inf a _](infComm); by move=> /(infab_leq_c (inf b c) a b).  (*inf a (inf b c) ≤ b*)
move: (infab_leq_ab b c); move=> /proj2; rewrite [inf a _](infComm); by move=> /(infab_leq_c (inf b c) a c).  (*inf a (inf b c) ≤ c*)
Qed.


(*Sólo esto es lo nuevo que he escrito*)


Definition reflexive (rel : L -> L -> Prop) : Prop := forall x :L, rel x x.
Definition antisymetric (rel : L -> L -> Prop) : Prop := forall x y : L, (rel x y) -> (rel y x) -> (x = y).
Definition transitive (rel : L -> L -> Prop) :Prop := forall x y z :L, rel x y -> rel y z -> rel x z.
Definition order (rel : L -> L -> Prop) := reflexive rel /\ antisymetric rel /\ transitive rel.


Lemma AlgToSet1 : forall a b : L, (a ∨ b = b) <-> (a ∧ b = a).
Proof.
split.
  move=> supab_b.
  have HL4d: a ∧ (a ∨ b ) = a.
    by apply: (L4d a b).
  by move: HL4d; rewrite supab_b.
move=> infab_a.
have HL4: b ∨ (a ∧ b) = b.
  by rewrite (L2d); apply: (L4 b a).
by move: HL4; rewrite infab_a; rewrite (L2).
Qed.

Variable nord : L -> L -> Prop.
Notation "x ≼ y" := (nord x y) (at level 50).
Hypothesis Nord: forall a b : L, (a ∨ b = b) <-> a ≼ b.

Lemma AlgToSet2: order nord.
split.
  (*La nueva relación es Reflexiva*)
  move=> a.
  have HL3 : a ∨ a = a.
    by apply: (L3 a).
  by move: (Nord a a); move=> /proj1 /(_ HL3).
split.
  (*La nueva relación es Antisimétrica*)
  move=> a b nleqab nleqba.
  have supa : (a ∨ b = a).
    by move: (Nord b a); move=> /proj2 /(_ nleqba); rewrite L2.
  have supb : (a ∨ b = b).
    by move: (Nord a b); move=> /proj2 /(_ nleqab)-supab_b.
  by move: supa; rewrite supb.
(*La nueva relación es Transitiva*)
move=> a b c.
move=> /(Nord a b)-supab /(Nord b c)-supbc; rewrite -(Nord a c).
by move: (L1 a b c); rewrite (supab); rewrite (supbc).
Qed.

Lemma AlgToSet3: forall z : L, (forall x y : L, (x ≼ z /\ y ≼ z) <-> x ∨ y ≼ z).
Proof.
move=> z x y.
split.
  move=> [H1 H2]; rewrite -(Nord (x ∨ y) z).
  have supxz: x ∨ z = z.
    by move: H1; rewrite -(Nord x z).
  have supyz: y ∨ z = z.
    by move: H2; rewrite -(Nord y z).
  by move: supxz; rewrite -{1}(supyz); rewrite -(L1 x y z).
move=> H1.
have cotaS: forall a b : L, (a ≼ (a ∨ b)) /\ (b ≼ (a ∨ b)).
  move=> a b.
  split.
    by rewrite -(Nord a ((a ∨ b))); rewrite -(L1 a a b); rewrite L3.
  by rewrite -(Nord b ((a ∨ b))); rewrite (L2 b (a ∨ b) ); rewrite (L1 a b b); rewrite L3.
have trasnord: forall x y z :L, nord x y -> nord y z -> nord x z.
    by move: AlgToSet2; move=> /proj2/proj2. 
split.
  move: H1; move: (cotaS x y); move=> /proj1.
  by apply: (trasnord x (x ∨ y) z ).
move: H1; move: (cotaS x y); move=> /proj2.
by apply: (trasnord y (x ∨ y) z ).
Qed.





