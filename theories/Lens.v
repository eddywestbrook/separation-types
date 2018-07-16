Require Export SepTypes.OrderedType.

(***
 *** Lenses
 ***)

(* A lens relating a "container" type A to a "component" type B *)
Record Lens (A B: Type) `{OType A} `{OType B} : Type :=
  {
    getL : A -> B;
    putL : B -> A -> A;
    proper_getL : Proper (oeq ==> oeq) getL;
    proper_putL : Proper (oeq ==> oeq ==> oeq) putL;
    lens_get_put : forall a, putL (getL a) a =o= a;
    lens_put_get : forall a b, getL (putL b a) =o= b;
    lens_put_put : forall a b1 b2, putL b2 (putL b1 a) =o= putL b2 a;
  }.

Arguments getL {A B _ _} _ _.
Arguments putL {A B _ _} _ _ _.
Arguments lens_get_put {A B _ _}.
Arguments lens_put_get {A B _ _}.
Arguments lens_put_put {A B _ _}.

Instance Proper_getL A B `{OType A} `{OType B} (l: Lens A B) :
  Proper (oeq ==> oeq) (getL l) :=
  proper_getL _ _ _.

Instance Proper_putL A B `{OType A} `{OType B} (l: Lens A B) :
  Proper (oeq ==> oeq ==> oeq) (putL l) :=
  proper_putL _ _ _.

(* Helper: combine a getL and a putL *)
Definition modifyL {A B} `{OType A} `{OType B} (l: Lens A B) (f: B -> B) (a:A) : A :=
  putL l (f (getL l a)) a.

Instance Proper_modifyL {A B} `{OType A} `{OType B} (l:Lens A B) f :
  Proper (oeq ==> oeq) f ->
  Proper (oeq ==> oeq) (modifyL l f).
Proof.
  intros prp_f a1 a2 eq_a. unfold modifyL.
  rewrite eq_a. reflexivity.
Qed.

(* The identity lens *)
Program Definition id_lens A `{OType A} : Lens A A :=
  {| getL := id;
     putL a a' := a; |}.
Next Obligation.
  intros a1 a2 Ra a1' a2' Ra'. assumption.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

(* Build a lens for the first element of a pair *)
Program Definition fst_lens A B `{OType A} `{OType B} : Lens (A*B) A :=
  {| getL := fst;
     putL a ab := (a, snd ab); |}.
Next Obligation.
  intros a1 a2 Ra ab1 ab2 Rab. rewrite Ra. rewrite Rab. reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

(* Build a lens for the second element of a pair *)
Program Definition snd_lens A B `{OType A} `{OType B} : Lens (A*B) B :=
  {| getL := snd;
     putL b ab := (fst ab, b); |}.
Next Obligation.
  intros b1 b2 Rb ab1 ab2 Rab. rewrite Rb. rewrite Rab. reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.


(* Compose two lenses *)
Program Definition compose_lens {A B C} `{OType A} `{OType B} `{OType C}
        (l1: Lens A B) (l2: Lens B C) : Lens A C :=
  {| getL a := getL l2 (getL l1 a);
     putL c a := putL l1 (putL l2 c (getL l1 a)) a;
  |}.
Next Obligation.
  intros a1 a2 Ra. rewrite Ra. reflexivity.
Defined.
Next Obligation.
  intros a1 a2 Ra c1 c2 Rc. rewrite Ra. rewrite Rc. reflexivity.
Defined.
Next Obligation.
  rewrite lens_get_put. rewrite lens_get_put. reflexivity.
Defined.
Next Obligation.
  rewrite lens_put_get. rewrite lens_put_get. reflexivity.
Defined.
Next Obligation.
  rewrite lens_put_put. rewrite lens_put_get. rewrite lens_put_put. reflexivity.
Defined.
