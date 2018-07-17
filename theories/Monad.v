Require Export SepTypes.OrderedType.
Require Export SepTypes.DownSet.


(***
 *** Monads over Ordered Types
 ***)

Class MonadOps (M: forall A `{OType A}, Type) : Type :=
  {
    returnM : forall {A} `{OType A}, A -> M A;
    bindM : forall {A B} `{OType A} `{OType B},
        M A -> (A -> M B) -> M B;
  }.

Class Monad (M: forall A `{OType A}, Type) `{OTypeF M} `{MonadOps M} : Prop :=
  {
    (* Proper-ness requirements *)
    Proper_returnM {A} `{OType A} :>
      Proper (oleq ==> oleq) (returnM (M:=M) (A:=A));
    Proper_bindM {A B} `{OType A} `{OType B} :>
      Proper (oleq ==> oleq ==> oleq) (bindM (M:=M) (A:=A) (B:=B));

    (* Standard monad laws, which require bind functions to be Proper *)
    monad_return_bind {A B} `{OType A} `{OType B} a (f : A -> M B) :
      Proper (oleq ==> oleq) f ->
      bindM (returnM a) f =o= f a;
    monad_bind_return {A} `{OType A} (m : M A) :
      bindM m returnM =o= m;
    monad_assoc {A B C} `{OType A} `{OType B} `{OType C}
                m (f: A -> M B) (g: B -> M C) :
      Proper (oleq ==> oleq) f ->
      Proper (oleq ==> oleq) g ->
      bindM (bindM m f) g =o= bindM m (fun x => bindM (f x) g);
  }.


Class MonadStateOps St `{OType St} (M: forall A `{OType A}, Type) : Type :=
  { getM : M St;
    putM : St -> M unit;
  }.

Class MonadState St `{OType St} (M: forall A `{OType A}, Type) `{OTypeF M}
      `{MonadOps M} `{MonadStateOps St M} : Prop :=
  {
    monad_state_monad :> Monad M;

    Proper_putM :> Proper (oleq ==> oleq) putM;

    monad_state_get :
      forall A `{OType A} (m : M A),
        bindM getM (fun _ => m) =o= m;

    monad_state_get_put :
      forall A `{OType A} (f : St -> unit -> M A),
        bindM getM (fun s => bindM (putM s) (f s))
        =o= bindM getM (fun s => f s tt);

    monad_state_put_get :
      forall A `{OType A} s (f : unit -> St -> M A),
        bindM (putM s) (fun u => bindM getM (f u))
        =o= bindM (putM s) (fun u => f u s);

    monad_state_put_put :
      forall A `{OType A} s1 s2 (f : unit -> unit -> M A),
        bindM (putM s1) (fun u => bindM (putM s2) (f u))
        =o= bindM (putM s2) (f tt)
  }.


Class MonadFixOps (M: forall A `{OType A}, Type) : Type :=
  {
    fixM : forall {A B} `{OType A} `{OType B},
      ((A -> M B) -> (A -> M B)) -> A -> M B;
  }.

Class MonadFix (M: forall A `{OType A}, Type)
      `{OTypeF M} `{MonadFixOps M} : Prop :=
  {
    Proper_fixM {A B} `{OType A} `{OType B} :>
      Proper (oleq ==> oleq) (fixM (M:=M) (A:=A) (B:=B));
    fixM_correct :
      forall {A B} `{OType A} `{OType B} (f: (A -> M B) -> (A -> M B)),
        Proper (oleq ==> oleq) f ->
        fixM f =o= f (fixM f)
  }.

Class MonadErrorOps (M: forall A `{OType A}, Type) : Type :=
  {
    errorM : forall {A} `{OType A}, M A;
  }.

Class MonadError (M: forall A `{OType A}, Type)
      `{OTypeF M} `{MonadOps M} `{MonadErrorOps M} : Prop :=
  {
    bindM_errorM :
      forall {A B} `{OType A} `{OType B} (f: A -> M B),
        bindM errorM f =o= errorM;
  }.


(***
 *** The Fixed-Point Monad
 ***)

Definition FixM A `{OType A} := DownSet A.

Instance OTypeF_FixM : OTypeF FixM := OType_DownSet.

Instance MonadOps_FixM : MonadOps FixM :=
  { returnM := fun _ _ => downClose;
    bindM := fun _ _ _ _ => bindDownSet }.

Instance Monad_FixM : Monad FixM.
Proof.
  constructor.
  - apply Proper_downClose.
  - apply Proper_bindDownSet.
  - intros; apply DownSet_return_bind; assumption.
  - intros; apply DownSet_bind_return; assumption.
  - intros; apply DownSet_assoc.
Qed.

Instance MonadFixOps_FixM : MonadFixOps FixM :=
  { fixM := fun _ _ _ _ => fixDownSet }.

Instance MonadFix_FixM : MonadFix FixM.
Proof.
  constructor.
  - intros. admit. (* FIXME: prove this, or fix the property *)
  - intros. apply fixDownSetUnfold. assumption.
Admitted.


(***
 *** The Fixed-Point State Monad
 ***)

(* FIXME... *)
