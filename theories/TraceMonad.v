Require Export SepTypes.OrderedType.
Require Export SepTypes.DownSet.
Require Export SepTypes.Monad.

Import ListNotations.


(***
 *** The Trace Monad = Final Algebra of Sets of Traces
 ***)

Definition TraceM St `{OType St} A `{OType A} :
  St -> DownSet (list St * option A).

FIXME HERE: finish this!
