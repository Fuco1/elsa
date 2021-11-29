;;; elsa-type-helpers.el --- Elsa type helpers -*- lexical-binding: t -*-

;; Copyright (C) 2017 Matúš Goljer

;; Author: Matúš Goljer <matus.goljer@gmail.com>
;; Maintainer: Matúš Goljer <matus.goljer@gmail.com>
;; Created: 6th June 2017
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

(require 'cl-generic)
(require 'eieio)

(require 'dash)
(require 'trinary)

(require 'elsa-types)
(require 'elsa-type-algebra)

(cl-defgeneric elsa-type-is-nil (type)
  "Test if TYPE is always nil.

Return trinary logic value.")

(cl-defmethod elsa-type-is-nil ((type elsa-type))
  (if (elsa-type-accept type (elsa-type-nil))
      (if (elsa-type-equivalent-p type (elsa-type-nil))
          (trinary-true)
        (trinary-maybe))
    (trinary-false)))

(cl-defgeneric elsa-type-is-non-nil (type)
  "Test if TYPE is always non-nil.

Return trinary logic value.")

(cl-defmethod elsa-type-is-non-nil ((type elsa-type))
  (if (elsa-type-accept type (elsa-type-nil))
      (if (elsa-type-equivalent-p type (elsa-type-nil))
          (trinary-false)
        (trinary-maybe))
    (trinary-true)))

(defun elsa--make-const-type (value)
  "Construct const type based on VALUE."
  (cond
   ((keywordp value)
    (elsa-const-type :type (elsa-make-type keyword) :value value))
   ((stringp value)
    (elsa-const-type :type (elsa-make-type string) :value value))
   ((integerp value)
    (elsa-const-type :type (elsa-make-type int) :value value))
   ((floatp value)
    (elsa-const-type :type (elsa-make-type float) :value value))
   ((symbolp value)
    (elsa-const-type :type (elsa-make-type symbol) :value value))
   (t (error "Trying to make a const type out of %S" value))))

(defun elsa--make-union-type (definition)
  (->> (-partition 1 definition)
       (-map 'elsa--make-type)
       (-reduce 'elsa-type-sum)))

(defun elsa--make-intersection-type (definition)
  (->> (-partition 1 definition)
       (-map 'elsa--make-type)
       (-reduce 'elsa-type-intersect)))

(defun elsa--make-type (definition)
  (pcase definition
    (`(readonly . ,type)
     (elsa-readonly-type :type (elsa--make-type type)))
    (`(const ,value)
     (elsa--make-const-type value))
    (`(cons) ;; mixed cons by default
     (elsa-type-cons :car-type (elsa-type-mixed)
                     :cdr-type (elsa-type-mixed)))
    (`(vector) ;; mixed vector by default
     (elsa-type-vector :item-type (elsa-type-mixed)))
    (`(list) ;; mixed list by default
     (let* ((item-type (elsa-type-mixed))
            (list-type (elsa-type-list :item-type item-type)))
       (oset list-type car-type item-type)
       (oset list-type cdr-type item-type)
       list-type))
    ((and def (guard (and (vectorp def)
                          (= (length def) 0))))
     (elsa-type-empty))
    (`(or . ,def)
     (elsa--make-union-type def))
    (`(and . ,def)
     (elsa--make-intersection-type def))
    (`(diff ,positive ,negative)
     (elsa-type-normalize
      (elsa-diff-type :positive (elsa--make-type (list positive))
                      :negative (elsa--make-type (list negative)))))
    (`(cons ,a ,b)
     (elsa-type-cons :car-type (elsa--make-type (list a))
                     :cdr-type (elsa--make-type (list b))))
    (`(list ,a)
     (let* ((item-type (elsa--make-type (list a)))
            (list-type (elsa-type-list :item-type item-type)))
       (oset list-type car-type item-type)
       (oset list-type cdr-type item-type)
       list-type))
    (`(&rest ,a)
     (let* ((item-type (elsa--make-type (list a)))
            (variadic-type (elsa-variadic-type :item-type item-type)))
       variadic-type))
    (`(vector ,a)
     (let* ((item-type (elsa--make-type (list a)))
            (vector-type (elsa-type-vector :item-type item-type)))
       vector-type))
    (`(function ,args ,ret)
     (elsa-function-type
      :args (-map 'elsa--make-type
                  (-let* (((positional rest)
                           (-split-with (lambda (x) (not (equal x '&rest))) args)))
                    (append (-partition 1 positional) (when rest (list rest)))))
      :return (elsa--make-type (list ret))))
    ((and `(,arg) (guard (and (atom arg)
                              (not (vectorp arg)))))
     (let* ((type-name (symbol-name arg))
            (constructor (intern (concat "elsa-type-" type-name))))
       (cond
        ((functionp constructor)
         (funcall constructor))
        (t (error "Unknown type %s" type-name)))))
    ((and `(,arg . nil))
     (elsa--make-type arg))))

(defmacro elsa-make-type (&rest definition)
  "Make a type according to DEFINITION. "
  `(elsa--make-type ',definition))

(defun elsa--eieio-class-parents-recursive (type)
  "Return all parents of TYPE."
  (cons type
        (-mapcat 'elsa--eieio-class-parents-recursive
                 (-map 'eieio-class-name (eieio-class-parents type)))))

(defun elsa-type-equivalent-p (this other)
  "Test if THIS and OTHER are equivalent types."
  (and (elsa-type-accept (elsa-get-type this) (elsa-get-type other))
       (elsa-type-accept (elsa-get-type other) (elsa-get-type this))))

;; TODO: what is the relationship of `a' and `a?'
(defun elsa-instance-of (this other)
  "Non-nil if THIS is instance of OTHER."
  (let ((this-type
         (eieio-object-class (if (symbolp this) (elsa--make-type (list this)) this)))
        (other-type
         (eieio-object-class (if (symbolp other) (elsa--make-type (list other)) other))))
    (not (null (memq other-type (elsa--eieio-class-parents-recursive this-type))))))

(defun elsa-type-nullable-p (type)
  "Test if TYPE is nullable (i.e. accepts nil)."
  (elsa-type-accept type (elsa-make-type nil)))

(defun elsa-type-make-nullable (type)
  "Make TYPE nullable."
  (elsa-type-sum type (elsa-make-type nil)))

(defun elsa-type-make-non-nullable (type)
  "Make TYPE non-nullable."
  (elsa-type-diff type (elsa-make-type nil)))

(cl-defgeneric elsa-type-normalize (type)
  "Normalize TYPE to its most simplest form.")

(cl-defmethod elsa-type-normalize ((this elsa-type))
  "Normalize a type.

Regular type normalizes to itself."
  this)

(cl-defmethod elsa-type-normalize ((this elsa-sum-type))
  "Normalize a sum type."
  (let ((types (--remove (elsa-type-accept (elsa-make-type empty) it)
                         (oref this types))))
    (cond
     ((not types)
      (elsa-type-empty))
     ((= 1 (length types))
      (car types))
     (t (elsa-sum-type :types types)))))

(cl-defmethod elsa-type-normalize ((this elsa-intersection-type))
  "Normalize an intersection type."
  (let ((types (--remove (elsa-type-accept it (elsa-make-type mixed))
                         (oref this types))))
    (cond
     ((= 1 (length types))
      (car types))
     (t (elsa-intersection-type :types types)))))

(cl-defmethod elsa-type-normalize ((this elsa-diff-type))
  "Normalize a diff type."
  (let ((pos (oref this positive))
        (neg (oref this negative)))
    (cond
     ((elsa-type-equivalent-p pos neg)
      (elsa-type-empty))
     ((elsa-type-equivalent-p neg (elsa-type-empty))
      (clone pos))
     ((not (elsa-type-accept pos neg))
      (clone pos))
     (t this))))

(provide 'elsa-type-helpers)
;;; elsa-type-helpers.el ends here
