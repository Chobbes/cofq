From Vellvm Require Import
     Numeric.Integers.

From QuickChick Require Import Show.

Instance showInt64 : Show Int64.int :=
  {| show := fun i => show (Int64.intval i)
  |}.
