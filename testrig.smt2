(set-info :status unknown)
(set-option :produce-models true)
; Logic is now "Whatever Z3 accepts" (set-logic AUFBV)

; Note to self: nothing achieved by changing from BV's to ints.

(declare-datatypes () ((TEAM t00 t01 t02 t03 t04 t05 t06 t07 t08 t09 t10 t11)))

; Declare a function taking a round, match, slot, and returns an integer
; indicating which team is at that slot.
(declare-fun sparticus ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)) TEAM)

; Parameterise some things
; FIXME: when teamcount doesn't fit in BV sort?
(define-fun team_count () (_ BitVec 4) (_ bv12 4))
(define-fun round_limit () (_ BitVec 4) (_ bv5 4))
(define-fun match_limit () (_ BitVec 4) (_ bv3 4))
(define-fun teams_per_round () (_ BitVec 4) (_ bv4 4))
(define-fun match_separation () (_ BitVec 4) (_ bv1 4))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round (_ BitVec 4)) (matcha (_ BitVec 4)) (matchb (_ BitVec 4)) (slota (_ BitVec 4)) (slotb (_ BitVec 4)))
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
;
;(declare-fun match_distinct ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)) Bool)
;(assert (forall ((round1 (_ BitVec 4)) (match1 (_ BitVec 4)) (slot1 (_ BitVec 4)) (round2 (_ BitVec 4)) (match2 (_ BitVec 4)) (slot2 (_ BitVec 4)))
;  (=> (match_distinct round1 match1 round2 match2)
;    (distinct (sparticus round1 match1 slot1) (sparticus round2 match2 slot2)
;))))
;
; Explicitly pump in match separation rather than logic it up.
(assert (forall ((round (_ BitVec 4)) (slota (_ BitVec 4)) (slotb (_ BitVec 4)))
  ; hardcode for 12 teams 3 matches, 1 round seperation
  (distinct (sparticus round (_ bv2 4) slota)
            (sparticus (bvadd round (_ bv1 4)) (_ bv0 4) slotb))))

(check-sat)
;(get-model)
