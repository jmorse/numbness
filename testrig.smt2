(set-info :status unknown)
(set-option :produce-models true)
(set-logic AUFBV)

; Declare a function taking a round, match, slot, and returns an integer
; indicating which team is at that slot.
(declare-fun sparticus ((_ BitVec 6) (_ BitVec 6) (_ BitVec 6)) (_ BitVec 6))

; Parameterise some things
; FIXME: when teamcount doesn't fit in BV sort?
(define-fun team_count () (_ BitVec 6) (_ bv32 6))
(define-fun round_limit () (_ BitVec 6) (_ bv13 6))
(define-fun match_limit () (_ BitVec 6) (_ bv8 6))
(define-fun teams_per_round () (_ BitVec 6) (_ bv4 6))

; Assert that for all slots, the outcome is in range.
(assert (forall ((round (_ BitVec 6)) (match (_ BitVec 6)) (slot (_ BitVec 6)))
    (bvult (sparticus round match slot) team_count)))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round (_ BitVec 6)) (matcha (_ BitVec 6)) (matchb (_ BitVec 6)) (slota (_ BitVec 6)) (slotb (_ BitVec 6)))
  (or (bvuge round round_limit)
  (or (bvuge matcha match_limit)
  (or (bvuge matchb match_limit)
  (or (bvuge slota teams_per_round)
  (or (bvuge slotb teams_per_round)
  ; Check they're not the same slot or match
  (or (and (= slota slotb) (= matcha matchb))
  ; Ensure they're distinct otherwise
  (distinct (sparticus round matcha slota) (sparticus round matchb slotb)
)))))))))

(check-sat)
;(get-model)
