%%% ====================================================================
%%% @LaTeX-file{
%%%    filename  = "mcom-l.cls",
%%%    version   = "2.01",
%%%    date      = "2007/06/18",
%%%    time      = "09:17:48 EDT",
%%%    checksum  = "31108 41 149 1479",
%%%    author    = "Michael Downes",
%%%    address   = "American Mathematical Society, PO Box 6248,
%%%                       Providence, RI 02940, USA",
%%%    email     = "tech-support@ams.org (Internet)",
%%%    supported = "yes",
%%%    abstract  = "This is a LaTeX documentclass for the AMS journal
%%%                 Mathematics of Computation.",
%%%    docstring = "The checksum field above contains a CRC-16 checksum
%%%                 as the first value, followed by the equivalent of
%%%                 the standard UNIX wc (word count) utility output
%%%                 of lines, words, and characters.  This is produced
%%%                 by Robert Solovay's checksum utility.",
%%% }
%%% ====================================================================

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{mcom-l}
              

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsart}}
\ProcessOptions\relax

\LoadClass{amsart}


\renewcommand{\datename}{Date:}
\newcommand{\Software}{\textsf{QuandleRUN}}
\newcommand{\magma}{\textsc{Magma}}
\newcommand{\rig}{\textsc{Rig}}
\newcommand{\cream}{\textsc{CREAM}}
\makeatletter
\def\@cite#1#2{[\textbf{#1\if@tempswa , #2\fi}]}
\def\@biblabel#1{[\textbf{#1}]}
\makeatother


\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}


\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\newtheorem{xca}[theorem]{Exercise}

\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}

\numberwithin{equation}{section}

\DeclareMathOperator{\Aut}{Aut}
\DeclareMathOperator{\Dis}{Dis}
\DeclareMathOperator{\LMlt}{LMlt}
\DeclareMathOperator{\Sub}{Sub}
\DeclareMathOperator{\Con}{Con}
\DeclareMathOperator{\Nil}{Nil}
%    Absolute value notation
\newcommand{\abs}[1]{\lvert#1\rvert}

%    Blank box placeholder for figures (to avoid requiring any
%    particular graphics capabilities for printing this document).
\newcommand{\blankbox}[2]{%
  \parbox{\columnwidth}{\centering
%    Set fboxsep to 0 so that the actual size of the box will match the
%    given measurements more closely.
    \setlength{\fboxsep}{0pt}%
    \fbox{\raisebox{0pt}[#2]{\hspace{#1}}}%
  }%
}
\newcommand{\alg}[3]{\ensuremath\mathbf{#1}=(#2,#3)}
\newcommand{\algebra}[1]{\ensuremath\mathbf{#1}}
\newcommand{\TODO}[1]{
    \begin{center}
    \fbox{\textcolor{red}{TODO: #1}}
    \end{center}
}

\newcommand{\WARNING}[1]{
    \begin{center}
    \fbox{\textcolor{red}{WARNING: #1}}
    \end{center}
}



\usepackage{pifont}
\usepackage[hidelinks]{hyperref}
\usepackage{listings}
\usepackage{graphicx}
\graphicspath{{images/}}
\usepackage{amssymb}
\usepackage[boxruled]{algorithm2e}
\usepackage{xcolor}
\usepackage{float}
\usepackage{caption}

\definecolor{codegreen}{rgb}{0,0.6,0}
\definecolor{codegray}{rgb}{0.5,0.5,0.5}
\definecolor{codepurple}{rgb}{0.58,0,0.82}
\definecolor{backcolour}{rgb}{0.95,0.95,0.92}
\definecolor{gold}{rgb}{1,0.75,0}
\definecolor{olivedrab1}{rgb}{0.75,1,0.24}
\lstdefinestyle{mystyle}{
    backgroundcolor=\color{backcolour},   
    commentstyle=\color{codegreen},
    keywordstyle=\color{magenta},
    numberstyle=\tiny\color{codegray},
    stringstyle=\color{codepurple},
    basicstyle=\ttfamily\footnotesize,
    breakatwhitespace=false,         
    breaklines=true,                 
    captionpos=b,                    
    keepspaces=true,                 
    numbers=left,                    
    numbersep=5pt,                  
    showspaces=false,                
    showstringspaces=false,
    showtabs=false,                  
    tabsize=2
}

\lstset{style=mystyle}



\endinput