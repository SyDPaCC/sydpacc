Require Extraction.

Extraction Blacklist List String Map Natint NatIntm.

Require Import ExtrOcamlBasic.

Extract Inductive nat => "Natint.nat" [ "Natint.O" "Natint.S" ].
