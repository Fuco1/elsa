;;; elsa-types.el --- Elsa types -*- lexical-binding: t -*-

;; Copyright (C) 2017 Matúš Goljer

;; Author: Matúš Goljer <matus.goljer@gmail.com>
;; Maintainer: Matúš Goljer <matus.goljer@gmail.com>
;; Created: 23rd March 2017
;; Keywords: languages, lisp

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'eieio)

(require 'dash)

(defclass elsa-type nil () :abstract t)

;; (elsa-type-describe :: (function (mixed) string))
(cl-defgeneric elsa-type-describe (type)
  "Return a string representation of TYPE."
  (format "%s" type))

(cl-defgeneric elsa-get-type (_thing)
  "Return type of THING."
  nil)

(cl-defmethod elsa-get-type ((this elsa-type))
  this)

(cl-defmethod elsa-type-describe ((this elsa-type))
  "Describe THIS type."
  (symbol-name (eieio-object-class this)))

;; (elsa-type-get-args :: (function (mixed) (list mixed)))
(cl-defgeneric elsa-type-get-args (_thing)
  "Get argument types of THING."
  nil)

(cl-defmethod elsa-type-get-return (_this)
  "Get return type of THIS type."
  nil)

(cl-defmethod elsa-type-get-return ((this elsa-type))
  "Get return type of THIS type."
  this)

(cl-defmethod elsa-type-accept ((this elsa-type) other)
  "Test if THIS type accepts OTHER.

Accepting in this context means that OTHER can be assigned to
THIS."
  (cond
   ((elsa-instance-of other this))
   ((and (elsa-readonly-type-p other)
         (elsa-type-accept this (oref other type))))
   ((and (elsa-const-type-p other)
         (elsa-type-accept this (oref other type))))
   ((and (elsa-type-list-p this)
         (elsa-type-nil-p other)))
   ((and (elsa-sum-type-p other)
         (-all? (lambda (other-type)
                  (elsa-type-accept this other-type))
                (oref other types))))
   (t nil)))

(cl-defmethod elsa-type-composite-p ((_this elsa-type))
  "Determine if the type is a composite type.

Composite types have to be wrapped in parens when passed as
arguments to other constructors."
  nil)

(cl-defmethod elsa-type-restrict-by ((_this elsa-type) _other)
  (error "Not implemented yet"))

(defclass elsa-type-unbound (elsa-type) ()
  :documentation "Type of an unbound variable.

This is not accepted by any type because we don't know what it is.")

(defclass elsa-type-empty (elsa-type) ()
  :documentation "Empty type.  Has no domain.

This is accepted by any type and does not accept any type.")

(cl-defmethod elsa-type-describe ((_this elsa-type-empty))
  "[]")

(cl-defmethod elsa-type-accept ((_this elsa-type-empty) other)
  (elsa-type-empty-p other))

(cl-defmethod elsa-type-accept ((_this elsa-type) (_this2 elsa-type-empty))
  t)

(cl-defmethod elsa-type-accept ((_this elsa-type-unbound) _other)
  "Unbound type accepts anything.

The only thing that can be of an unbound type is a symbol
representing a variable.  It can accept anything because it is
not bound to any specific value yet."
  t)

(cl-defmethod elsa-type-describe ((_this elsa-type-unbound))
  "unbound")

(defclass elsa-intersection-type (elsa-type)
  ((types :initform nil :initarg :types))
  :documentation "Intersection type.

This type is an intersection of multiple types.

It can accept any type that is all the types of the intersection.

It is accepted by any of the intersected types because it is all
of them.")

(cl-defmethod elsa-type-composite-p ((_this elsa-intersection-type)) t)

(cl-defmethod clone ((this elsa-intersection-type))
  "Make a deep copy of a intersection type."
  (let ((types (-map 'clone (oref this types)))
        (new (cl-call-next-method this)))
    (oset new types types)
    new))

(cl-defmethod elsa-type-accept ((this elsa-intersection-type) other)
  (-all? (lambda (type) (elsa-type-accept type other)) (oref this types)))

(defclass elsa-sum-type (elsa-type)
  ((types :type list
          :initarg :types
          :initform nil))
  :documentation "Sum type.

This type is a combination of other types.

It can accept any type that is accepted by at least one of its
summands.

It is accepted by any type that is all of the summed types
because the actual type can be any of them.")

(cl-defmethod elsa-type-describe ((this elsa-sum-type))
  (cond
   ;; TODO: this should be really handled by the normalization step, a
   ;; sum type Mixed | <...> => Mixed, possibly without Nil
   ((elsa-type-accept this (elsa-type-mixed))
    "mixed")
   (t
    (format "(or %s)" (mapconcat 'elsa-type-describe (oref this types) " ")))))

(cl-defmethod elsa-type-composite-p ((_this elsa-sum-type)) t)

(cl-defmethod clone ((this elsa-sum-type))
  "Make a deep copy of a sum type."
  (let ((types (-map 'clone (oref this types)))
        (new (cl-call-next-method this)))
    (oset new types types)
    new))

(cl-defmethod elsa-type-accept ((this elsa-sum-type) other)
  (cond
   ((= 0 (length (oref this types))) nil)
   ((elsa-sum-type-p other)
    (-all? (lambda (ot) (elsa-type-accept this ot)) (oref other types)))
   (t (-any? (lambda (ot) (elsa-type-accept ot other)) (oref this types)))))

(defclass elsa-diff-type (elsa-type)
  ((positive :initform (elsa-type-mixed) :initarg :positive)
   (negative :initform (elsa-type-empty) :initarg :negative))
  :documentation "Diff type.

This type is a combination of positive and negative types.  It
can accept any type that is accepted by at least one positive
type and none of the negative types.")

(cl-defmethod clone ((this elsa-diff-type))
  "Make a deep copy of a diff type."
  (let ((positive (clone (oref this positive)))
        (negative (clone (oref this negative)))
        (new (cl-call-next-method this)))
    (oset new positive positive)
    (oset new negative negative)
    new))

(cl-defmethod elsa-type-accept ((this elsa-diff-type) (other elsa-type))
  (and (elsa-type-accept (oref this positive) other)
       (not (elsa-type-accept other (oref this negative)))))

(cl-defmethod elsa-type-describe ((this elsa-diff-type))
  (if (oref this negative)
      (format "(diff %s %s)"
              (elsa-type-describe (oref this positive))
              (elsa-type-describe (oref this negative)))
    (elsa-type-describe (oref this positive))))

(defclass elsa-type-t (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-t))
  "t")

(defclass elsa-type-nil (elsa-type) ())

(cl-defmethod elsa-type-accept ((_this elsa-type-nil) (other elsa-type))
  (elsa-type-nil-p other))

(cl-defmethod elsa-type-describe ((_this elsa-type-nil))
  "nil")

(defclass elsa-type-symbol (elsa-type) ()
  :documentation "Quoted symbol")

(cl-defmethod elsa-type-describe ((_this elsa-type-symbol))
  "symbol")

(defclass elsa-type-bool (elsa-type elsa-type-symbol) ())

(cl-defmethod elsa-type-accept ((_this elsa-type-bool) other)
  (or (elsa-type-bool-p other)
      (elsa-type-accept
       (elsa-sum-type
        :types (list (elsa-type-t) (elsa-type-nil)))
       other)))

(cl-defmethod elsa-type-describe ((_this elsa-type-bool))
  "bool")

;; Mixed type is special in that it is always created nullable.  Mixed
;; can also serve as bool type in Emacs Lisp.
(defclass elsa-type-mixed (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-mixed))
  "mixed")

(cl-defmethod elsa-type-accept ((_this elsa-type-mixed) other)
  ;; Since the specialization on the first argument runs first, the
  ;; (type form) signature from elsa-reader.el is never invoked.  We
  ;; will therefore "manually" dispatch, or rather resolve, the second
  ;; argument from a form to a type here.
  (when (elsa-form-child-p other)
    (setq other (elsa-get-type other)))
  (unless (elsa-type-child-p other)
    (error "Other must be `elsa-type-child-p'"))
  (not (eq (eieio-object-class other) 'elsa-type-unbound)))

(defclass elsa-type-sequence (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-sequence))
  "sequence")

(cl-defmethod elsa-type-get-item-type ((_this elsa-type))
  "Get the type of items of a sequence type."
  nil)

(defclass elsa-type-string (elsa-type-sequence) ())

(cl-defmethod elsa-type-get-item-type ((_this elsa-type-string))
  "Get the type of items of a sequence type."
  (elsa-type-int))

(defclass elsa-type-short-string (elsa-type-string) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-string))
  "string")

(defclass elsa-type-buffer (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-buffer))
  "buffer")

(defclass elsa-type-frame (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-frame))
  "frame")

(defclass elsa-type-number (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-number))
  "number")

(defclass elsa-type-int (elsa-type-number) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-int))
  "int")

(defclass elsa-type-float (elsa-type-number) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-float))
  "float")

(defclass elsa-type-marker (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-marker))
  "marker")

(defclass elsa-type-keyword (elsa-type-symbol) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-keyword))
  "keyword")

(defclass elsa-type-cons (elsa-type)
  ((car-type :type elsa-type :initarg :car-type
             :initform (elsa-type-mixed))
   (cdr-type :type elsa-type :initarg :cdr-type
             :initform (elsa-type-mixed))))

(cl-defmethod clone ((this elsa-type-cons))
  "Make a deep copy of a cons type."
  (let ((car-type (clone (oref this car-type)))
        (cdr-type (clone (oref this cdr-type)))
        (new (cl-call-next-method this)))
    (oset new car-type car-type)
    (oset new cdr-type cdr-type)
    new))

(cl-defmethod elsa-type-accept ((this elsa-type-cons) (other elsa-type-cons))
  "A cons type accepts another cons type covariantly.

That means that iff both arguments of this are supertypes of
other, then this is a supertype of other."
  (and (elsa-type-accept (oref this car-type) (oref other car-type))
       (elsa-type-accept (oref this cdr-type) (oref other cdr-type))))

(cl-defmethod elsa-type-composite-p ((_this elsa-type-cons)) t)

(cl-defmethod elsa-type-describe ((this elsa-type-cons))
  (format "(cons %s %s)"
          (elsa-type-describe (oref this car-type))
          (elsa-type-describe (oref this cdr-type))))

(defclass elsa-type-list (elsa-type-cons elsa-type-sequence)
  ((item-type :type elsa-type
              :initarg :item-type
              :initform (elsa-type-mixed))))

(cl-defmethod clone ((this elsa-type-list))
  "Make a deep copy of a list type."
  (let ((item-type (clone (oref this item-type)))
        (new (cl-call-next-method this)))
    (oset new item-type item-type)
    new))

(cl-defmethod elsa-type-describe ((this elsa-type-list))
  (format "(list %s)" (elsa-type-describe (oref this item-type))))

(cl-defmethod elsa-type-composite-p ((_this elsa-type-list)) t)

(cl-defmethod elsa-type-get-item-type ((this elsa-type-list))
  "Get the type of items of a sequence type."
  (oref this item-type))

(defclass elsa-type-vector (elsa-type-sequence)
  ((item-type :type elsa-type
              :initarg :item-type
              :initform (elsa-type-mixed))))

(cl-defmethod clone ((this elsa-type-vector))
  "Make a deep copy of a vector type."
  (let ((item-type (clone (oref this item-type)))
        (new (cl-call-next-method this)))
    (oset new item-type item-type)
    new))

(cl-defmethod elsa-type-composite-p ((_this elsa-type-vector)) t)

(cl-defmethod elsa-type-describe ((this elsa-type-vector))
  (format "(vector %s)" (elsa-type-describe (oref this item-type))))

(cl-defmethod elsa-type-get-item-type ((this elsa-type-vector))
  "Get the type of items of a sequence type."
  (oref this item-type))

(defclass elsa-variadic-type (elsa-type-list) nil)

(cl-defmethod elsa-type-describe ((this elsa-variadic-type))
  (format "&rest %s" (elsa-type-describe (oref this item-type))))

(defclass elsa-function-type (elsa-type)
  ((args :type list :initarg :args)
   (return :type elsa-type :initarg :return)))

(cl-defmethod clone ((this elsa-function-type))
  "Make a deep copy of a function type."
  (let ((args (-map 'clone (oref this args)))
        (return (clone (oref this return)))
        (new (cl-call-next-method this)))
    (oset new args args)
    (oset new return return)
    new))

(cl-defmethod elsa-type-describe ((this elsa-function-type))
  (format "(function (%s) %s)"
          (mapconcat 'elsa-type-describe (oref this args) " ")
          (elsa-type-describe (oref this return))))

(cl-defmethod elsa-type-accept ((this elsa-function-type) other)
  (when (elsa-function-type-p other)
    ;; Argument types must be contra-variant, return types must be
    ;; co-variant.
    (catch 'ok
      (let ((this-args (oref this args))
            (other-args (oref other args)))
        (unless (= (length this-args) (length other-args))
          (throw 'ok nil))
        (cl-mapc
         (lambda (this-arg other-arg)
           (unless (elsa-type-accept other-arg this-arg)
             (throw 'ok nil)))
         this-args other-args)
        (unless (elsa-type-accept
                 (elsa-type-get-return this)
                 (elsa-type-get-return other))
          (throw 'ok nil)))
      t)))

(cl-defmethod elsa-type-composite-p ((_this elsa-function-type)) t)

;; (elsa-function-type-nth-arg :: (function (int mixed) mixed))
(defun elsa-function-type-nth-arg (n elsa-type)
  (let* ((args (oref elsa-type args))
         (type (nth n args)))
    (cond
     ((eq type nil)
      (let ((last-type (-last-item args)))
        (when (elsa-variadic-type-p last-type)
          (oref last-type item-type))))
     ((elsa-variadic-type-p type)
      (oref type item-type))
     (t type))))

(cl-defmethod elsa-type-get-args ((this elsa-function-type))
  "Get argument types of THIS function type."
  (oref this args))

(cl-defmethod elsa-type-get-return ((this elsa-function-type))
  "Get return type of THIS type."
  (oref this return))

(defclass elsa-generic-type (elsa-type)
  ((label :type symbol :initarg :label)))

(cl-defmethod clone ((this elsa-generic-type))
  "Make a deep copy of a generic type."
  (let ((label (oref this label))
        (new (cl-call-next-method this)))
    (oset new label label)
    new))

(cl-defmethod elsa-type-describe ((this elsa-generic-type))
  (symbol-name (oref this label)))

;; One-dimensional sparse arrays indexed by characters
(defclass elsa-type-chartable (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-chartable))
  "chartable")

;; One-dimensional arrays of t or nil.
(defclass elsa-type-boolvector (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-boolvector))
  "boolvector")

;; Super-fast lookup tables
(defclass elsa-type-hashtable (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-hashtable))
  "hashtable")

;; Compound objects with programmer-defined types
(defclass elsa-type-record (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-record))
  "record")

;; Buffers are displayed in windows
(defclass elsa-type-window (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-window))
  "window")

;; A terminal device displays frames
(defclass elsa-type-terminal (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-terminal))
  "terminal")

;; Recording the way a frame is subdivided
(defclass elsa-type-windowconfiguration (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-windowconfiguration))
  "windowconfiguration")

;; Recording the status of all frames
(defclass elsa-type-frameconfiguration (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-frameconfiguration))
  "frameconfiguration")

;; A subprocess of Emacs running on the underlying OS
(defclass elsa-type-process (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-process))
  "process")

;; A thread of Emacs Lisp execution
(defclass elsa-type-thread (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-thread))
  "thread")

;; An exclusive lock for thread synchronization
(defclass elsa-type-mutex (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-mutex))
  "mutex")

;; Condition variable for thread synchronization
(defclass elsa-type-conditionvariable (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-conditionvariable))
  "conditionvariable")

;; Receive or send characters
(defclass elsa-type-stream (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-stream))
  "stream")

;; What function a keystroke invokes
(defclass elsa-type-keymap (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-keymap))
  "keymap")

;; How an overlay is represented
(defclass elsa-type-overlay (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-overlay))
  "overlay")

;; Fonts for displaying text
(defclass elsa-type-font (elsa-type) ())

(cl-defmethod elsa-type-describe ((_this elsa-type-font))
  "font")

(defclass elsa-const-type (elsa-type)
  ((type :type elsa-type :initarg :type)
   (value :initarg :value)))

(cl-defmethod elsa-type-describe ((this elsa-const-type))
  (format "(const %S)" (oref this value)))

(cl-defmethod elsa-type-composite-p ((_this elsa-const-type)) t)

(cl-defmethod elsa-type-accept ((this elsa-const-type) other)
  "The const type is different from readonly in that a readonly
type can never be assigned to but a const type is only a
narrowing of a type to a concrete value from the type's domain."
  (and (elsa-const-type-p other)
       (elsa-type-equivalent-p (oref this type) (oref other type))
       (equal (oref this value) (oref other value))))

;; Readonly type for defconst
(defclass elsa-readonly-type (elsa-type)
  ((type :type elsa-type :initarg :type)))

(cl-defmethod elsa-type-accept ((_this elsa-readonly-type) _other)
  nil)

(cl-defmethod elsa-type-describe ((this elsa-readonly-type))
  (format "(readonly %s)" (elsa-type-describe (oref this type))))

(provide 'elsa-types)
;;; elsa-types.el ends here
