

(declare-sort Char)
(define-sort Str () (Array Int Char))
(echo "Simulating signed 128 bit number domain...")
(echo "(including GNU C int128 (2's complement) and IEEE 754 binary128 overflow but excluding underflow)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html#g_t_005f_005fint128)")
(echo "(https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#IEEE_754_quadruple-precision_binary_floating-point_format:_binary128)")
(define-fun MAX_MAX_INT () Int 9223372036854775807)  ;RangeDegradeMAX
(declare-fun MAX_INT () Int)                  ;RangeDegradeParam
(define-fun MIN_MAX_INT () Int 0)                     ;RangeDegradeMIN
(define-fun MIN_INT () Int (- (- MAX_INT) 1))
(define-fun MAX_REAL () Real (* (^ 2.0 1023) (- 2.0 (^ 2.0 (- 52)))))
(define-fun MIN_REAL () Real (- MAX_REAL))
;avoiding +/-/*/division/modulo overflow
(define-fun add_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (+ _1 _2))(<= (+ _1 _2) MAX_INT)
	))
(define-fun sub_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (- _1 _2))(<= (- _1 _2) MAX_INT)
))
(define-fun mul_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (* _1 _2))(<= (* _1 _2) MAX_INT)
))
(define-fun div_guard ((_1 Int)(_2 Int)) Bool (and 
	(not (= _2 0))
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
))
(define-fun mod_guard ((_1 Int)(_2 Int)) Bool (and 
	(div_guard _1 _2)
))
(declare-datatypes (PT_) ((Pointer 
				NULL
				Void
				(prim (value PT_))
				(ptr (addr Pointer)))))
(declare-sort PT)
(declare-sort Void)
(declare-fun pt2i (PT) Int)
(declare-fun i2pt (Int) PT)
(declare-fun r2pt (Real) PT)
(declare-fun b2pt (Bool) PT)
(define-fun point ((_p (Pointer PT))) (Pointer PT) 
				  (ite (is-ptr _p) (addr _p) _p) 
) 
(declare-fun depoint (PT) (Pointer PT))
(declare-const _v PT)
(declare-const _p (Pointer PT)) 
(assert (iff (= (depoint _v) _p) (= _v (value _p))))

(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2 () Int)
(declare-fun indexSet_127_DRB005-indirectaccess1-orig-yes_c_null_FUNCTION () (Array Int Int))
(declare-fun xa1_128_DRB005-indirectaccess1-orig-yes_c_0_null_FUNCTION (Int ) Real)
(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD1 () Int)
(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD2 () Int)
(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_t_FUNCTION () Int)
(declare-fun idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION () Int)
(declare-fun base_107_DRB005-indirectaccess1-orig-yes_c_CONST () (Pointer Void))
(declare-fun nthreads () Int)
(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_chunk_size () Int)
(declare-fun _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1 () Int)
(declare-fun i_125_4482_DRB005-indirectaccess1-orig-yes_c_FUNCTION () Int)
(define-fun main ((argc_103_DRB005-indirectaccess1-orig-yes_c Int)(argv_103_DRB005-indirectaccess1-orig-yes_c (Pointer (Pointer Void)))) Int (ite (= base_107_DRB005-indirectaccess1-orig-yes_c_CONST (r2pt 0)) 1 0))
(declare-fun malloc (Int) PT)

(define-fun ParallelCondition () Bool (and 

(and (and (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2) (< _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1 nthreads) (< _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2 nthreads) (not (= _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2)) (not (= _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD1 _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD2)) (< 0 _125_DRB005-indirectaccess1-orig-yes_c_t_FUNCTION nthreads) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1)) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2 MAX_INT) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_FUNCTION MAX_INT) (<= 1 nthreads MAX_INT) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1 MAX_INT) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD1 MAX_INT) (<= 0 _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD2 MAX_INT))
(<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2 MAX_INT)
(<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_FUNCTION MAX_INT)
(<= 1 nthreads MAX_INT)
(<= 0 _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD1 MAX_INT)
(<= 0 _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD1 MAX_INT)
(<= 0 _125_DRB005-indirectaccess1-orig-yes_c_chunk_THREAD2 MAX_INT)
))

;_LB,     _1,    _UB
(define-fun InCarryInRange ((_1 Int)(_LB Int)(_UB Int)) Bool (and
  (<= _LB _1)(<= _1 _UB)
))
(define-fun InCarryInRangeUB ((_1 Int)(_UB Int)) Bool (or
  (= _1 _UB)
  (< _1 _UB)
))
(define-fun InCarryInRangeLB ((_1 Int)(_LB Int)) Bool (or
  (= _1 _LB)
  (> _1 _LB)
))

(echo "Range down-grade...")
;RangeDegradeUB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeUB _1 9223372036854775807))
;RangeDegradeIn(define-fun InRange ((_1 Int)) Bool (InCarryInRange _1 0 9223372036854775807))
;RangeDegradeLB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeLB _1 0))
;RangeDegradeParams(assert (InRange nthreads))

(assert ParallelCondition)

(assert (= (xa1_128_DRB005-indirectaccess1-orig-yes_c_0_null_FUNCTION idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION i_125_4482_DRB005-indirectaccess1-orig-yes_c_FUNCTION) (+ (xa1_128_DRB005-indirectaccess1-orig-yes_c_0_null_FUNCTION idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION) (+ 1.0 i_125_4482_DRB005-indirectaccess1-orig-yes_c_FUNCTION))))
(assert (<= MIN_INT _125_DRB005-indirectaccess1-orig-yes_c_t_THREAD2 MAX_INT))
(assert (<= MIN_INT idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION MAX_INT))
(assert (<= 0 i_125_4482_DRB005-indirectaccess1-orig-yes_c_FUNCTION 179))
(assert (= idx_127_DRB005-indirectaccess1-orig-yes_c_FUNCTION (select indexSet_127_DRB005-indirectaccess1-orig-yes_c_null_FUNCTION i_125_4482_DRB005-indirectaccess1-orig-yes_c_FUNCTION)))

(check-sat)
(get-model)
(exit)