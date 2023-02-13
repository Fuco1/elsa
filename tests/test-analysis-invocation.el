;; -*- lexical-binding: t -*-
(require 'elsa-test-helpers)

(require 'elsa-analyser)

(describe "elsa--analyse-function-like-invocation"

  (describe "overloads"

    (it "should resolve to only one overload based on the matching argument"
      (let ((state (elsa-state)))
        (elsa-state-add-defun state
          (elsa-defun :name 'b
                      :type (elsa-make-type
                             (and (function (vector) vector)
                                  (function (sequence) sequence)))
                      :arglist '(x)))
        (elsa-test-with-analysed-form "|(b [asd])" form
          :state state
          (expect form :to-be-type-equivalent (elsa-make-type vector))))))


  (describe "number of arguments"

    (it "should report error if not enough arguments are passed"
      (let ((state (elsa-state)))
        (elsa-state-add-defun state
          (elsa-defun :name 'b
                      :type (elsa-make-type (function (int) mixed))
                      :arglist '(x)))
        (elsa-test-with-analysed-form "|(b)" form
          :state state
          :errors-var errors
          (expect (car errors)
                  :message-to-match "Function `b' expects at least 1 argument but received 0"))))

    (it "should report error if more arguments are passed than supported"
      (let ((state (elsa-state)))
        (elsa-state-add-defun state
          (elsa-defun :name 'b
                      :type (elsa-make-type (function (int) mixed))
                      :arglist '(x)))
        (elsa-test-with-analysed-form "|(b 1 2)" form
          :state state
          :errors-var errors
          (expect (length errors) :to-equal 2)
          (expect (cadr errors)
                  :message-to-match "Function `b' expects at most 1 argument but received 2")))))


  (describe "resolving expression type of funcall with type guard"

    (it "should resolve the type of expression to t if the type matches the guard"
      (elsa-test-with-analysed-form "|(integerp 1)" form
        (expect form :to-be-type-equivalent (elsa-make-type t))))

    (it "should resolve the type of expression to nil if the type can never match the guard"
      (elsa-test-with-analysed-form "|(integerp :keyword)" form
        (expect form :to-be-type-equivalent (elsa-make-type nil))))

    (it "should resolve the type of expression to bool if we don't know"
      (let ((state (elsa-state)))
        (elsa-state-add-defvar state 'a (elsa-make-type mixed))
        (elsa-test-with-analysed-form "|(integerp a)" form
          :state state
          (expect form :to-be-type-equivalent (elsa-make-type bool))))))

  (describe "resolving narrowed type of variable in a predicate"

    (it "should narrow the type of a variable to the predicated type"
      (let ((state (elsa-state)))
        (elsa-state-add-defvar state 'a (elsa-make-type mixed))
        (elsa-test-with-analysed-form "|(and (integerp a) a)" form
          :state state
          (expect (elsa-nth 2 form) :to-be-type-equivalent (elsa-make-type int)))))))
