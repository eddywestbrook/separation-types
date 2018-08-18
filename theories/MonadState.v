Require Export SepTypes.OrderedType.
Require Export SepTypes.Monad.


(***
 *** Monads with State Effects
 ***)

(* State effects = get and put *)
Class MonadStateOps M `{OTypeF M} St `{OType St} : Type :=
  {
    get_ofun : M St _ ;
    put_ofun : St -o> M unit _
  }.

Notation oget := (oconst get_ofun).
Notation oput := (oconst put_ofun).


Class MonadState M {FOM:OTypeF M} St {OSt: OType St}
      `{@MonadOps M FOM} `{@MonadStateOps M FOM St OSt} : Prop :=
  {
    monad_state_monad :> Monad M;

    monad_state_get_raw :
      forall {ctx A} `{OType A} (m : OExpr ctx (M A _)),
        obind @o@ oget @o@ (ofun s => ovar m) =o= m;

    monad_state_get_get_raw :
      forall {ctx A} `{OType A} (f:OExpr ctx _),
        obind @o@ oget @o@ (ofun s1 =>
                            obind @o@ oget @o@ (ofun s2 =>
                                                ovar f @o@ ovar s1 @o@ ovar s2))
        =o= obind @o@ oget @o@ (ofun s1 => ovar f @o@ s1 @o@ s1);

    monad_state_get_put_raw :
      forall {ctx A} `{OType A} (f : OExpr ctx _),
        obind @o@ oget @o@ (ofun s => obind @o@ (oput @o@ ovar s)
                                            @o@ (ovar f @o@ ovar s))
        =o=
        obind @o@ oget @o@ (ofun s => ovar f @o@ ovar s @o@ ott);

    monad_state_put_get_raw :
      forall {ctx A} `{OType A} s (f: OExpr ctx _),
        obind @o@ (oput @o@ ovar s) @o@
              (ofun u => obind @o@ oget @o@ (ovar f @o@ ovar u))
        =o= obind @o@ (oput @o@ ovar s)
                  @o@ (ofun u => ovar f @o@ ovar u @o@ ovar s);

    monad_state_put_put_raw :
      forall {ctx A} `{OType A} (s1 : OExpr ctx _) s2
             (f: OExpr ctx (unit -o> unit -o> M A _)),
        obind @o@ (oput @o@ ovar s1)
              @o@ (ofun u => obind @o@ (oput @o@ ovar s2) @o@ (ovar f @o@ ovar u))
        =o= obind @o@ (oput @o@ ovar s2) @o@ (ovar f @o@ ott)
  }.


Lemma monad_state_get `{MonadState} {ctx A} `{OType A} (m : OExpr ctx (M A _))
      (m': OExpr (ctx :> St) (M A _))
      {w:WeakensTo m (PreExtendsToBase _) m'} :
  obind @o@ oget @o@ (ofun s => m') =o= m.
Proof.
  etransitivity; [ | apply monad_state_get_raw ].
  f_equiv. apply mkLamExt. symmetry. apply w.
Qed.

Lemma monad_state_get_get `{MonadState} {ctx A} `{OType A}
      (f: OExpr (ctx :> St) St -> OExpr (ctx :> St) (St -o> M A _))
      (* {w:WeakensTo f (PreExtendsToBase _) f'} *) :
  obind @o@ oget @o@ (ofun (s1:St) => obind @o@ oget @o@ (f s1))
  =o= obind @o@ oget @o@ (ofun (s1:St) => (f s1) @o@ ovar s1).
Proof.
  transitivity (obind @o@ oget
                      @o@ (ofun s1 =>
                           obind @o@ oget
                                 @o@ (ofun s2 =>
                                      ovar (ofun s => f s) @o@ ovar s1
                                           @o@ ovar s2))).
  - f_equiv. apply mkLamExt. f_equiv. rewrite <- ofunEta. apply mkLamExt.
    f_equiv.
    apply funOExt; intro celem. simpl. destruct celem. simpl. destruct c; simpl.
    reflexivity.
  - rewrite monad_state_get_get_raw. f_equiv. apply mkLamExt.
    apply funOExt; intro celem. simpl. destruct celem. reflexivity.
Qed.

Lemma monad_state_get_put `{MonadState} {ctx A} `{OType A}
      (f : OExpr (ctx :> St) St -> OExpr (ctx :> St) (unit -o> M A _)) :
  obind @o@ oget @o@ (ofun s => obind @o@ (oput @o@ ovar s) @o@ (f s))
  =o=
  obind @o@ oget @o@ (ofun s => f s @o@ ott).
Proof.
  transitivity (obind @o@ oget
                      @o@ (ofun s =>
                           obind @o@ (oput @o@ ovar s)
                                 @o@ (ovar (ofun x => f x) @o@ ovar s))).
  - f_equiv. apply mkLamExt. f_equiv. apply funOExt; intro celem. simpl.
    destruct celem; reflexivity.
  - rewrite monad_state_get_put_raw. f_equiv. apply mkLamExt.
    apply funOExt; intro celem; simpl. destruct celem. reflexivity.
Qed.


FIXME HERE NOW: finish writing these more useful versions of the state laws


    monad_state_put_get :
      forall {ctx A} `{OType A} s s'
             (f : OExpr (ctx :> _) (unit -o> St -o> M A _))
             {w: WeakensTo s (PreExtendsToBase _) s'},
        obind @o@ (oput @o@ s) @o@
              (ofun u => obind @o@ oget @o@ (f @o@ ovar u))
        =o= obind @o@ (oput @o@ s) @o@ (ofun u => f @o@ ovar u @o@ s');

    monad_state_put_put :
      forall {ctx A} `{OType A} s1 s2 s2'
             (f : OExpr (ctx :> _) _) f'
             {wf: WeakensTo f (PreExtendsToBase _) f'}
             {ws2: WeakensTo s2 (PreExtendsToBase _) s2'},
        obind @o@ (oput @o@ s1)
              @o@ (ofun u => obind @o@ (oput @o@ s2') @o@ (f' @o@ u))
        =o= obind @o@ (oput @o@ s2) @o@ (f @o@ ott)


(***
 *** The State Monad Laws for OExprs
 ***)

(*
FIXME HERE NOW: cannot match weakenOExpr on the LHS; instead, we need a
Strengthens typeclass for lifting m out of its context

FIXME HERE NOW: also need a rule for unquoting 

Lemma monad_state_get_OExpr
      {ctx} `{ValidCtx ctx} `{MonadState} {A} `{OType A}
      m {validM: @ValidOExpr ctx (M A _ _) _ m} :
  App (App (Embed bindM) (Embed getM)) (Lam (weakenOExpr 0 _ m)) =e= m.
Proof.
  apply unquote_eq. intro. simpl. apply monad_state_get.
Qed.

Lemma monad_state_get_put_OExpr
      {ctx} `{ValidCtx ctx} `{MonadState} {A} `{OType A}
      f {validF: @ValidOExpr _ (St -o> unit -o> M A _ _) _ f} :
  App (App (Embed bindM) (Embed getM))
      (Lam (App (App (Embed bindM) (App (Embed putM) (Var OVar_0)))
                (Lam (App (App f )))))
*)


(***
 *** The State Monad Transformer
 ***)

Definition StateT St `{OType St} M `{OTypeF1 M} A `{OType A} :=
  St -o> M (St * A)%type _.

Instance OTypeF1_StateT St `{OType St} M `{OTypeF1 M} :
  OTypeF1 (StateT St M) :=
  fun _ _ => _.

(*
Instance FindOTypeF1_StateT St `{OType St} M `{FindOTypeF1 M} :
  FindOTypeF1 (StateT St M) (fun _ _ => _) := I.
*)

Instance MonadOps_StateT St `{OType St} M `{MonadOps M} : MonadOps (StateT St M) :=
  {returnM :=
     fun A _ => ofun x => ofun s => returnM @o@ (s ,o, x);
   bindM :=
     fun A B _ _ =>
       ofun m => ofun f => ofun s =>
         (do s_x <- (m @o@ s);
            f @o@ (osnd @o@ s_x) @o@ (ofst @o@ s_x))
  }.


(* The Monad instance for StateT *)
Instance Monad_StateT St `{OType St} M `{Monad M} : Monad (StateT St M).
Proof.
  constructor; intros.
  - osimpl.
  - osimpl.
  - osimpl.
Qed.

(***
 *** Monads of Stateful Computation
 ***)

