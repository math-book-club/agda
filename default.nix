{ nixpkgs ? import <nixpkgs> {} }:

let
  agda = nixpkgs.haskellPackages.Agda;
  agda-stdlib = nixpkgs.AgdaStdlib;
  emacs = nixpkgs.emacsWithPackages
    (p: with p; [ use-package
      evil
      evil-surround
      agda2-mode
      company
      rainbow-delimiters
      gruvbox-theme
    ]);
  ghc = agda.compiler;

in
  nixpkgs.mkShell {
    name = "agda-shell";
    buildInputs = [ emacs agda agda-stdlib ];
    shellHook = ''
      export HOME=$(pwd)
      mkdir -p .emacs.d
      cat > .emacs.d/init.el << EOF
      (package-initialize)

      (require 'agda2-mode nil t)

      ;; EVIL configuration
      (when (require 'evil) nil t (evil-mode 1))
      (use-package evil-surround
        :ensure t
        :config
        (global-evil-surround-mode 1))

      (evil-define-key 'normal agda2-mode-map "gd" 'agda2-goto-definition-keyboard)

      ;; Completion/code navigation config
      (add-hook 'after-init-hook 'global-company-mode)

      ;; Theme and display sanity
      (load-theme 'gruvbox t)
      (menu-bar-mode -1)
      (tool-bar-mode -1)

      (load-file (let ((coding-system-for-read 'utf-8))
                      (shell-command-to-string "agda-mode locate")))

      (custom-set-variables
        '(agda2-program-args (quote ("-i" "${agda-stdlib}/share/agda/" )))
      )
      (custom-set-faces
       '(agda2-highlight-catchall-clause-face     ((t (:box (:line-width 2 :color "#ffffff" :style 'released-button) :foreground "#ffffff"))))
       '(agda2-highlight-coinductive-constructor-face ((t (:foreground "#b8bb26")))) ;; neutral_green
       '(agda2-highlight-coverage-problem-face    ((t (:box (:line-width 2 :color "#ebdbb2" :style 'released-button) :foreground "#ebdbb2"))))
       '(agda2-highlight-data-type-face           ((t (:foreground "#83a598"))))
       '(agda2-highlight-datatype-face            ((t (:foreground "#61ACBB")))) ;; turquoise4
       '(agda2-highlight-deadcode-face            ((t (:background "#bbaa97"))))
       '(agda2-highlight-error-face               ((t (:underline t :foreground "#9d0006"))))
       '(agda2-highlight-field-face               ((t (:foreground "#b16286"))))
       '(agda2-highlight-function-face            ((t (:foreground "#83a598")))) ;; neutral_blue
       '(agda2-highlight-inductive-constructor-face   ((t (:foreground "#b8bb26")))) ;; neutral_green
       '(agda2-highlight-keyword-face             ((t (:foreground "#af3a03")))) ;; faded_orange
       '(agda2-highlight-macro-face               ((t (:foreground "#458588"))))
       '(agda2-highlight-module-face              ((t (:foreground "#d3869b")))) ;; bright_purple
       '(agda2-highlight-number-face              ((t (:foreground "#b57614")))) ;; faded_yellow
       '(agda2-highlight-positivity-problem-face  ((t (:box (:line-width 2 :color "#fb4933" :style 'released-button))))) ;; bright_red
       '(agda2-highlight-postulate-face           ((t (:foreground "#fb4933")))) ;; bright_red
       '(agda2-highlight-primitive-face           ((t (:foreground "#076678")))) ;; faded_blue
       '(agda2-highlight-primitive-type-face      ((t (:foreground "#61ACBB")))) ;; turquoise4
       '(agda2-highlight-record-face              ((t (:foreground "#83a598")))) ;; neutral_blue
       '(agda2-highlight-string-face              ((t (:foreground "#79740e")))) ;; faded_green
       '(agda2-highlight-symbol-face              ((t (:foreground "#d5c4a1"))))
       '(agda2-highlight-termination-problem-face ((t (:background "#d3869b"))))
       '(agda2-highlight-typechecks-face          ((t (:foreground "#000000" :background "#ebdbb2"))))
       '(agda2-highlight-unsolved-constraint-face ((t (:box (:line-width 2 :color "#fb4933" :style 'released-button))))) ;; bright_red
       '(agda2-highlight-unsolved-meta-face       ((t (:box (:line-width 2 :color "#fb4933" :style 'released-button))))) ;; bright_red
      )
      EOF
      export AGDA_STDLIB="${agda-stdlib}/share/agda"
    '';
  }
