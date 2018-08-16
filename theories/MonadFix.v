Require Export SepTypes.Monad.

(***
 *** Monads with Fixed-points
 ***)

Class MonadFixOps M `{OTypeF M} : Type :=
  { fix_ofun : forall {A B} `{OType A} `{OType B},
      ((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _); }.

Notation ofix := (oconst fix_ofun).
(*
Definition ofix {ctx} `{MonadFixOps} {A B} `{OType A} `{OType B} :
  OExpr ctx (((A -o> M B _) -o> (A -o> M B _)) -o> (A -o> M B _)) :=
  oconst fix_ofun.
*)

Class MonadFix M {OF:OTypeF M} `{@MonadOps M OF} `{@MonadFixOps M OF} : Prop :=
  { Monad_MonadFix :> Monad M;
    FixedPoint_ofix :
      forall {ctx A B} `{OType A} `{OType B}
             (f: OExpr ctx ((A -o> M B _) -o> (A -o> M B _))),
        ofix @o@ f =o= f @o@ (ofix @o@ f)
  }.

Class MonadBottomOps M `{OTypeF M} : Type :=
  { bottom_ofun : forall {A} `{OType A}, M A _ }.

Notation obottom := (oconst bottom_ofun).
(*
Definition obottom {ctx} `{MonadBottomOps} {A} `{OType A} : OExpr ctx (M A _) :=
  oconst bottom_ofun.
*)

Class MonadBottom M {OF:OTypeF M} `{@MonadOps M OF}
      `{@MonadBottomOps M OF} : Prop :=
  { Monad_MonadBottom :> Monad M;
    Bottom_MonadBottom : forall {ctx A} `{OType A} (m: OExpr ctx (M A _)),
        obottom <o= m }.
