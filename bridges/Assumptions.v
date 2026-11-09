(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The bridges rest on no axiom, only on the definitions of both
    sides: Rocq answers "Closed under the global context" for each, and
    the flake's check requires that answer. *)

From Deduxit.Linear.Bridges Require NanoYallaBridge NanoIllBridge.

Print Assumptions Deduxit.Linear.Bridges.NanoYallaBridge.ll_iff_nanoll.
Print Assumptions Deduxit.Linear.Bridges.NanoYallaBridge.nanoll_iff_ll.
Print Assumptions Deduxit.Linear.Bridges.NanoIllBridge.ill_iff_nanoill.
Print Assumptions Deduxit.Linear.Bridges.NanoIllBridge.nanoill_iff_ill.
