From Coq Require Import Logic.
From mathcomp Require Import all_ssreflect.


Definition reflexive {T : Type} (rel : T -> T -> Prop) : Prop := forall x :T, rel x x.
Definition antisymetric {T : Type} (rel : T -> T -> Prop) : Prop := forall x y : T, (rel x y) -> (rel y x) -> (x = y).
Definition transitive {T : Type} (rel : T -> T -> Prop) :Prop := forall x y z :T, rel x y -> rel y z -> rel x z.
Definition order {T : Type} (rel : T -> T -> Prop) := reflexive rel /\ antisymetric rel /\ transitive rel.


Structure ordtype (T : Type) := Ordtype { ord :> T -> T -> Prop;
                                          reflex : reflexive ord;
                                          antisym : antisymetric ord;
                                          trans : transitive ord  }.

Structure jointype {T : Type} (ord_T : ordtype T) := Jointype 
  { joint :> T -> T -> T;
     JH : (forall z : T , forall x y : T,  (ord_T x z /\ ord_T y z) <-> ord_T ( joint x y) z) }.

Structure meettype {T : Type} (ord_T : ordtype T) := Meettype 
  { meett :> T -> T -> T;
     MH : (forall z : T , forall x y : T,  (ord_T z x /\ ord_T z y) <-> ord_T z ( meett x y)) }.


Lemma ab_leq_jab {T : Type} (ord : ordtype T) (join : jointype ord)
                    : forall a b : T ,  ord a (join a b) /\ ord b (join a b) .
Proof.
move=> a b.
split.
  by move: (reflex T ord (join a b)); rewrite -(JH ord join (join a b) a b); move=> /proj1.
by move: (reflex T ord (join a b)); rewrite -(JH ord join (join a b) a b); move=> /proj2.
Qed.

Lemma mab_leq_ab {T : Type} (ord : ordtype T) (meet : meettype ord)
                    : forall a b : T ,  ord (meet a b) a /\ ord (meet a b) b.
Proof.
move=> a b.
split.
  by move: (reflex T ord (meet a b)); rewrite -(MH ord meet (meet a b) a b); move=> /proj1.
by move: (reflex T ord (meet a b)); rewrite -(MH ord meet (meet a b) a b); move=> /proj2.
Qed.


Lemma ConnectJ {T : Type} (ord : ordtype T) (join : jointype ord)
                    : forall a b : T ,  ord a b <-> (join a b = b).
Proof.
split.
move=> abLeq.
  apply: (antisym T ord (join a b) b ).
    rewrite -(JH ord join b a b).
    split.
      by [].
    by apply: (reflex T ord b ).
  move: (reflex T ord (join a b)).
  by rewrite -(JH ord join (join a b) a b); move=> /proj2.
move=> H.
move: (reflex T ord (join a b)).
rewrite {2}H.
move: (ab_leq_jab ord join a b); move=> /proj1.
by apply: (trans T ord a (join a b) b).
Qed.

Lemma ConnectM {T : Type} (ord : ordtype T) (meet : meettype ord)
                    : forall a b : T ,  ord a b <-> (meet a b = a).
Proof.
split.
move=> abLeq.
apply: (antisym T ord (meet a b) a ).
  move: (reflex T ord (meet a b)).
  by rewrite -(MH ord meet (meet a b) a b); move=> /proj1.
rewrite -(MH ord meet a a b).
split.
  by apply: (reflex T ord a).
by [].
move=> H.
move: (mab_leq_ab ord meet a b); move=> /proj2.
move: (reflex T ord (meet a b)).
rewrite {1}H.
by apply: (trans T ord a (meet a b) b).
Qed.

(* Propiedades L1 a L4*)

Lemma L3 {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a : L , join a a = a.
Proof.
move=> a.
move: (reflex L ord a). 
by move=> /(ConnectJ ord join a a).
Qed.

Lemma L3d {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord)  : forall a : L , meet a a = a.
Proof.
move=> a.
move: (reflex L ord a). 
by move=> /(ConnectM ord meet a a).
Qed.


Lemma L2 {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b : L , join a b = join b a.
Proof.
move=> a b.
apply: (antisym L ord (join a b)  (join b a)). (*Por Antisimetría*)
  move: (ab_leq_jab ord join b a); move=> /and_comm.
  by rewrite (JH ord join (join b a) a b). 
move: (ab_leq_jab ord join a b); move=> /and_comm.
by rewrite (JH ord join (join a b) b a).
Qed.



Lemma L2d {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b : L , meet a b = meet b a.
Proof.
move=> a b.
apply: (antisym L ord (meet a b)  (meet b a)). (*Por Antisimetría*)
  move: (mab_leq_ab ord meet a b); move=> /and_comm.
  by rewrite (MH ord meet (meet a b) b a). 
move: (mab_leq_ab ord meet b a); move=> /and_comm.
by rewrite (MH ord meet (meet b a) a b).
Qed.


Lemma L4 {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b : L , join a (meet a b) = a.
Proof.
move=> a b.
move: (mab_leq_ab ord meet a b); move=> /proj1. (*Vemos que inf a b ≤ a *)
move=> /(ConnectJ ord join (meet a b) a). (*Aplicamos el Connecting Lemma para ver que inf a b ∨ a = a*)
by rewrite L2.
Qed.

Lemma L4d {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b : L , meet a (join a b) = a.
Proof.
move=> a b.
move: (ab_leq_jab ord join a b); move=> /proj1. (*Vemos que a ≤ sup a b *)
by move=> /(ConnectM ord meet a (join a b) ). (*Aplicamos el Connecting Lemma para ver que sup a b ∧ a = a*)
Qed.

Lemma L1 {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b c : L , join (join a b) c = join a (join b c).
Proof. 
have c_leq_jab: forall x y z : L , ord z y -> ord z (join x y).
    move=>x y z z_leq_y; move: (ab_leq_jab ord join x y); move=> /proj2; move: z_leq_y; by apply: (trans L ord z y (join x y) ).
move=> a b c.
apply: (antisym L ord (join (join a b) c) (join a (join b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(JH ord join (join a (join b c)) (join a b) c).
  split.
    rewrite -(JH ord join (join a (join b c)) a b).
    split.
      move: (ab_leq_jab ord join a (join b c)); by move=> /proj1. (*1° caso a ≤ sup a (sup b c)*)
    move: (ab_leq_jab ord join b c); move=> /proj1; by move=> /(c_leq_jab a (join b c) b). (*2° caso b ≤ sup a (sup b c)*)
  move: (ab_leq_jab ord join b c); move=> /proj2; by move=> /(c_leq_jab a (join b c) c). (*c ≤ sup a (sup b c)*)
rewrite -(JH ord join (join (join a b) c) a (join b c)).
split.
  rewrite (L2 ord join meet).
  move: (ab_leq_jab ord join a b); move=> /proj1.
  by move=> /(c_leq_jab c (join a b) a).
rewrite -(JH ord join (join (join a b) c ) b c).
split.
  move: (ab_leq_jab ord join a b); move=> /proj2. rewrite [join _ c](L2 ord join meet).
  by move=> /(c_leq_jab c (join a b) b).  (*sup c (sup a b)*)
move: (ab_leq_jab ord join (join a b) c); by move=> /proj2. (*c ≤ sup (sup a b) c*)
Qed.


Lemma L1d {L : Type} (ord : ordtype L) (join : jointype ord) (meet : meettype ord) : forall a b c : L , meet (meet a b) c = meet a (meet b c).
Proof. 
have mab_leq_c: forall x y z : L , ord x z -> ord (meet x y) z.
    move=>x y z H0; move: (mab_leq_ab ord meet x y); move=> /proj1-H1; move: H1 H0; by apply: (trans L ord (meet x y) x z ).
move=> a b c.
apply: (antisym L ord (meet (meet a b) c) (meet a (meet b c))).  (*Veremos que son iguales por antisimetría*)
  rewrite -(MH ord meet (meet (meet a b) c) a (meet b c) ).
  split.
    move: (mab_leq_ab ord meet a b); move=> /proj1; by move=> /(mab_leq_c (meet a b) c a). (*inf (inf a b) c ≤ a*)
  rewrite -(MH ord meet (meet (meet a b) c) b c ).
  split.
    move: (mab_leq_ab ord meet a b); move=> /proj2; by move=> /(mab_leq_c (meet a b) c b).  (*inf (inf a b) c ≤ b*)
  move: (mab_leq_ab ord meet (meet a b) c); by move=> /proj2.
rewrite -(MH ord meet (meet a (meet b c)) (meet a b) c ).
split.
  rewrite -(MH ord meet (meet a (meet b c)) a b ).
  split.
    move: (mab_leq_ab ord meet a (meet b c)); by move=> /proj1.  (*inf a (inf b c) ≤ a*)
  move: (mab_leq_ab ord meet b c); move=> /proj1; rewrite [meet a _](L2d ord join meet); by move=> /(mab_leq_c (meet b c) a b).  (*inf a (inf b c) ≤ b*)
move: (mab_leq_ab ord meet b c); move=> /proj2; rewrite [meet a _](L2d ord join meet); by move=> /(mab_leq_c (meet b c) a c).  (*inf a (inf b c) ≤ c*)
Qed.


(*Cosas nuevas*)



Definition ordPreserv {L K : Type} (ord_L: ordtype L) (ord_K: ordtype K) (f : L -> K) := forall a b : L, ord_L a b -> ord_K (f a) (f b).


Definition joinPreserv {L K : Type} {ord_L: ordtype L} {ord_K: ordtype K} 
                       (join_L : jointype ord_L) (join_K : jointype ord_K) (f : L -> K)
                       := forall x y : L, ord_K (join_K (f x) (f y)) (f ( join_L x y)) .


Definition meetPreserv {L K : Type} {ord_L: ordtype L} {ord_K: ordtype K} 
                       (meet_L : meettype ord_L) (meet_K : meettype ord_K) (f : L -> K)
                       := forall x y : L, ord_K (f ( meet_L x y)) (meet_K (f x) (f y)) .


Lemma prop219i1 {L K : Type} (ord_L: ordtype L) (ord_K: ordtype K)
              (join_L : jointype ord_L) (join_K : jointype ord_K) (f : L -> K)
              : ordPreserv ord_L ord_K f <-> joinPreserv join_L join_K f.
Proof.
split.
  unfold ordPreserv; move=> ordenP.
  unfold joinPreserv; move=> a b.
  have cotainf : ord_L a (join_L a b) /\ ord_L b (join_L a b).
    move: (reflex L ord_L (join_L a b) ).
    by move=> /(JH ord_L join_L (join_L a b) a b ).
  move: cotainf; move=> [cota_a cota_b].
  move: cota_a; move=> /(ordenP a (join_L a b)) cota_fa.
  move: cota_b; move=> /(ordenP b (join_L a b)) cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (JH ord_K join_K (f (join_L a b)) (f a) (f b) ).
unfold joinPreserv; move=> H.
unfold ordPreserv; move=> a b /((ConnectJ ord_L join_L a b))-jab_L.
move: (H a b); rewrite jab_L.
move: (ab_leq_jab ord_K join_K (f a) (f b)); move=> /proj1.
by apply: (trans K ord_K (f a) (join_K (f a) (f b)) (f b) ).
Qed.


Lemma prop219i2 {L K : Type} (ord_L: ordtype L) (ord_K: ordtype K)
              (meet_L : meettype ord_L) (meet_K : meettype ord_K) (f : L -> K)
              : ordPreserv ord_L ord_K f <-> meetPreserv meet_L meet_K f.
Proof.
split.
  unfold ordPreserv; move=> ordenP.
  unfold meetPreserv; move=> a b.
  move: (mab_leq_ab ord_L meet_L a b); move=> [cota_a cota_b].
  move: cota_a; move=> /(ordenP (meet_L a b) a) cota_fa.
  move: cota_b; move=> /(ordenP (meet_L a b) b) cota_fb.
  move: (conj cota_fa cota_fb).
  by rewrite (MH ord_K meet_K (f (meet_L a b)) (f a) (f b) ).
unfold meetPreserv; move=> H.
unfold ordPreserv; move=> a b /((ConnectM ord_L meet_L a b))-mab_L.
move: (mab_leq_ab ord_K meet_K (f a) (f b)); move=> /proj2.
move: (H a b); rewrite mab_L.
by apply: (trans K ord_K (f a) (meet_K (f a) (f b)) (f b) ).
Qed.











