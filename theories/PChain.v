Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Wf.

Require Import SepTypes.OrderedType SepTypes.OFuns.

Open Scope ofun_scope.


(** Diagrams in the category of ordered types. *)
Section pDiagram.
  Class OTypeSequence (f : nat -> Type) : Type :=
    oTypeSeq :> forall n, OType (f n).
  Class PDiagram (f : nat -> Type) {o : OTypeSequence f} : Type :=
    proj : forall n, f (S n) -o> f n.

  (** "Projective limit" chains. *)
  Record PChain f `{PDiagram f} : Type :=
    { chain : forall n, f n
    ; chainCondition : forall n, chain n =o= proj n @@ (chain (S n)) }.
End pDiagram.

Arguments chain {_ _ _}.

Instance OTPChain f `{PDiagram f} : OType (PChain f) :=
  {| oleq := fun s1 s2 => forall n, chain s1 n <o= chain s2 n |}.
Proof.
  constructor.
  - intros ?; reflexivity.
  - intros ?; etransitivity; eauto.
Defined.

Program Definition chainProj {F} `{PDiagram F} n : PChain F -o> F n :=
  {| ofun_app := fun c => chain c n |}.
Next Obligation. firstorder. Qed.

Lemma chain_inv F `{PDiagram F} (c1 c2 : PChain F) :
  c1 =o= c2 -> forall n, chain c1 n =o= chain c2 n.
Proof. firstorder. Qed.


(** Product diagrams. *)
Section productPDiagram.
  Definition ProductTypeSequence (f1 f2 : nat -> Type) : nat -> Type :=
    fun n => prod (f1 n) (f2 n).

  Global Instance ProductOTypeSequence f1 f2
           {o1 : OTypeSequence f1} {o2 : OTypeSequence f2}
    : OTypeSequence (ProductTypeSequence f1 f2) :=
    fun n => OTpair _ _ _ _.

  Global Instance ProductPDiagram f1 f2
         `{PDiagram f1} `{PDiagram f2}
    : PDiagram (ProductTypeSequence f1 f2) :=
    fun n => pair_ofun (proj n ∘ fst_ofun) (proj n ∘ snd_ofun).
End productPDiagram.

Lemma product_proper A B `(OType A) `(OType B) (a c : A) (b d : B) :
  a =o= c ->
  b =o= d ->
  (a, b) =o= (c, d).
Proof. firstorder. Qed.

Lemma product_inv A B `(OType A) `(OType B) (a c : A) (b d : B) :
  (a, b) =o= (c, d) ->
  a =o= c /\ b =o= d.
Proof. firstorder. Qed.


(** The following two operations and subsequent proofs are used in the
    fold and unfold morphisms of the product functor. *)

(* Zip together two chains to form a single product chain. *)
Program Definition zipPChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
        PChain f1 * PChain f2 -o> PChain (ProductTypeSequence f1 f2) :=
  {| ofun_app :=
       fun p =>
         {| chain := fun n => (chain (fst p) n, chain (snd p) n) |} |}.
Next Obligation.
  apply product_proper.
  - destruct p; auto.
  - destruct p0; auto.
Qed.
Next Obligation. firstorder. Qed.

(* Unzip a product chain into two separate chains. *)
Program Definition unzipPChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
  PChain (ProductTypeSequence f1 f2) -o> PChain f1 * PChain f2 :=
  {| ofun_app :=
       fun f =>
         ({| chain := fun n => fst (chain f n) |},
          {| chain := fun n => snd (chain f n) |}) |}.
Next Obligation.
  destruct f; simpl; eapply product_inv in chainCondition0;
    apply chainCondition0.
Qed.
Next Obligation.
  destruct f; simpl; eapply product_inv in chainCondition0;
    apply chainCondition0.
Qed.
Next Obligation. intros f g Heq; split; intros n; apply Heq. Qed.

(* Zip and unzip are an isomorphism. *)
Lemma zip_unzip_PChain f1 f2 `{PDiagram f1} `{PDiagram f2} :
  @zipPChain f1 f2 _ _ _ _ ∘ @unzipPChain f1 f2 _ _ _ _ =o= id_ofun.
Proof.
  split; intros c1 c2 Hleq n; apply Hleq.
Qed.

Lemma unzip_zip_PChain f1 f2 `{PDiagram f1} `{PDiagram f2} :
  @unzipPChain f1 f2 _ _ _ _ ∘ zipPChain =o= id_ofun.
Proof.
  split; intros [] [] []; split; simpl; try apply H1; apply H2.
Qed.


(** Mapping a natural transformation over a PChain. This is used for
    defining the unLeaf and unNode operations on chains. *)
Section pChainMap.
  Context f1 `{PDiagram f1} f2 `{PDiagram f2}
          (α : forall n, f1 n -o> f2 n)
          (* A specialized naturality condition. *)
          (α_natural : forall n, α n ∘ proj n =o= proj n ∘ α (S n)).

  Program Definition pChainMap : PChain f1 -o> PChain f2 :=
    {| ofun_app :=
         fun c =>
           {| chain := fun n => α n @@ (chain c n) |} |}.
  Next Obligation.
    assert (H1: proj n @@ (α (S n) @@ chain c (S n)) =
                (proj n ∘ α (S n)) @@ chain c (S n)) by auto.
    rewrite H1, <- α_natural; destruct c as [c Hc]; rewrite Hc; reflexivity.
  Qed.
  Next Obligation.
    intros ? ? Heq n; simpl in *;
      destruct (α n); apply ofun_Proper; apply Heq.
  Qed.
End pChainMap.
