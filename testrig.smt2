(set-info :status unknown)
(set-option :produce-models true)
; Logic is now "Whatever Z3 accepts" (set-logic AUFBV)

; Note to self: nothing achieved by changing from BV's to ints.

(declare-datatypes () ((TEAM t00 t01 t02 t03 t04 t05 t06 t07 t08 t09 t10 t11
t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23
t24 t25 t26 t27 t28 t29 t30 t31)))

; Declare a function taking a round, match, slot, and returns an integer
; indicating which team is at that slot.
(declare-fun sparticus ((_ BitVec 4) (_ BitVec 4) (_ BitVec 2)) TEAM)

; Parameterise some things
; FIXME: when teamcount doesn't fit in BV sort?
(define-fun round_limit () (_ BitVec 4) (_ bv4 4))
(define-fun match_limit () (_ BitVec 4) (_ bv8 4))
(define-fun match_separation () (_ BitVec 4) (_ bv1 4))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round (_ BitVec 4)) (matcha (_ BitVec 4)) (matchb (_ BitVec 4)) (slota (_ BitVec 2)) (slotb (_ BitVec 2)))
  (or (bvuge round round_limit)
  (or (bvuge matcha match_limit)
  (or (bvuge matchb match_limit)
  ; Check they're not the same slot or match
  (or (and (= slota slotb) (= matcha matchb))
  ; Ensure they're distinct otherwise
  (distinct (sparticus round matcha slota) (sparticus round matchb slotb)
)))))))

; Explicitly pump in match separation rather than logic it up.
(assert (forall ((round (_ BitVec 4)) (slota (_ BitVec 2)) (slotb (_ BitVec 2)) (slotc (_ BitVec 2)))
  ; hardcode for 32 teams 8 matches, 1 round seperation
  (let ((nextround (bvadd round (_ bv1 4))))
  (and
     (distinct (sparticus round (_ bv6 4) slota)
              (sparticus round (_ bv7 4) slotb)
              (sparticus nextround (_ bv0 4) slotc))
     (distinct (sparticus round (_ bv7 4) slota)
              (sparticus nextround (_ bv0 4) slotb)
              (sparticus nextround (_ bv1 4) slotc))))))

(check-sat)
;(get-model)
