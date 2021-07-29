# WashingMachineSPL

The goal of this project is to build a Washing Machine Software Product Line . First, I encoded the washing machine SFP in SMT using Z3, then, Using Alloy,an open source language and analyzer for software modeling,
I modeled the washing machine component architecture and finally, I combined the two models and created a rough script to verify whether the feauture model always had the following property:
" Startwash is always followed by EndWash", or starting the Washing machine will always eventually end to it stoping the wash
