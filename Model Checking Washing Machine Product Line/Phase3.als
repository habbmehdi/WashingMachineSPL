/*-------------------------Signatures---------------------------*/

abstract sig Feature {} {this in AbstractDiagram.FeatureSet}

abstract sig Socket {} {this in AbstractDiagram.Sockets}

abstract sig Ball{}{this in AbstractDiagram.Balls}

abstract sig Link  {
	L : Socket -> Ball
}{
	this in AbstractDiagram.DelegatedLink
	L not = none -> none
}

abstract sig  Component {}{this in AbstractDiagram.Comps}



abstract sig AbstractDiagram {
	Comps : set Component,
	Sockets : set Socket,
	Balls : set Ball,
	SocketPorts : Comps -> Sockets,
	BallPorts : Comps -> Balls,
	DelegatedLink : set Link,
	FeatureSet : set Feature
}

/*-------------------------Constraints---------------------------*/


// a socket cannot exist if it is not linked to a ball
fact { 
	all ad : AbstractDiagram, s : Socket | s in ad.Sockets implies some l : Link, b : Ball | l.L = s->b and l in ad.DelegatedLink
}

// Component connected to a ball cannot exist if is not connected to a socket
fact {
	all c:Component, b:Ball, ad: AbstractDiagram | c->b in ad.BallPorts and c in ad.Comps and b in ad.Balls implies some s : Socket, l : Link|
		l.L = s->b and l in ad.DelegatedLink
}

// A delegated link can only exist if the socket and balls exist
fact{
	all l: Link, ad : AbstractDiagram | l in ad.DelegatedLink implies some s : Socket, b : Ball | s in ad.Sockets and b in ad.Balls and l.L=s->b
}

//two components cannot have the same socket
fact {
	all disj a,b : Component, ad : AbstractDiagram | disj [a.(ad.SocketPorts), b.(ad.SocketPorts)]
}

//two components cannot have the same ball
fact {
	all disj a,b : Component, ad : AbstractDiagram  | disj [a.(ad.BallPorts), b.(ad.BallPorts)]
}

//two sockets cannot be connected to the same ball
fact {
	all disj a,c : Socket, b : Ball , ad : AbstractDiagram, d : Link|
		 (d in ad.DelegatedLink and b in a.(d.L) and b in ad.Balls and a in ad.Sockets and c in ad.Sockets ) implies not b in c.(d.L)
}

// a component socket cannot connect to istelf via its own ball
fact {
	all a : Component , b : Socket, c : Ball , ad : AbstractDiagram|
		b in a.(ad.SocketPorts) and c in a.(ad.BallPorts) implies all d : Link|
			 not c in b.(d.L)
}

// all sockets must be connected to a Component
fact {	
	all a: Socket, ad : AbstractDiagram | 
	a in ad.Sockets implies some b : Component | b in ad.Comps and a in b.(ad.SocketPorts)
}

// all balls must be connected to some component
fact {	
	all a: Ball, ad : AbstractDiagram | 
	a in ad.Balls implies some b : Component | b in ad.Comps and a in b.(ad.BallPorts)
}

/*-----------------------------------Software Product Line Of Washing Machine-----------------------------------------------------*/

lone sig dri,hri,tri,tdri extends Socket {} 

lone sig dpi,hpi,tpi,tdpi extends Ball {} 

lone sig cd,ch,ct,dt extends Link {}


lone sig MainController,Heater,Timer,Dryer extends Component {} 

lone sig Delay,Heat,Dry extends Feature{} 

//Heat feature constraint
fact{ 
 	 (not #Heat = 1 implies not (#Heater = 1 or #dpi=1 or #cd=1)) and (#Heat = 1 implies #dri = 1 )
}

//Dry feauture constraint
fact{
	 (not #Dry = 1 implies not (#ch = 1 or #hpi=1 or #Dryer=1 or #tdri=1 or #dt=1 or #tdpi=1)) and 
		(#Dry = 1 implies  (#hri = 1 and #tdri = 1) )
}

//Delay feauture constraint
fact{
	(not #Delay=1 implies not(#ct=1 or #tpi=1)) and (#Delay = 1 implies #tri = 1)
}

//Timer constraint
fact{
	#Timer=1 implies (#Delay=1 or #Dry=1)
}

//Delay and heat exclusivity
fact{
	not(#Delay = 1 and #Heat=1)
}

// Assignment of MainControllers sockets,balls and links
pred MCSB [ad : AbstractDiagram]{ 

	(MainController.(ad.SocketPorts) = dri + hri + tri) and (cd.L = dri -> dpi) and (ch.L = hri -> hpi) and (ct.L = tri -> tpi)

}

// Assignment of Heaters sockets,balls and links
pred HSB [ad : AbstractDiagram]{ 

	Heater.(ad.BallPorts) = dpi

}

// Assignment of Timers sockets,balls and links
pred TSB [ad : AbstractDiagram]{ 

	Timer.(ad.BallPorts) = tpi + tdpi

}


// Assignment of Dryers sockets, balls and links 
pred DSB [ad : AbstractDiagram]{

	Dryer.(ad.BallPorts) = hpi and Dryer.(ad.SocketPorts) = tdri and dt.L = tdri -> tdpi

}


pred P2{

	all f : Feature, ad : AbstractDiagram |
		(MCSB[ad] and HSB[ad] and TSB[ad] and DSB[ad]) and  f in ad.FeatureSet implies some c : Component | 
			c in ad.Comps and some s : Socket, b:Ball, l : Link |
				s in MainController.(ad.SocketPorts) and b in c.(ad.BallPorts) and l.L = s->b and l in ad.DelegatedLink

}
// check P2 for 4 but exactly 1 AbstractDiagram

pred W1 {

#Heat = 0 // Heat to change
#Dry = 0 // Dry to change
#Delay = 0 // Delay to change
	
all ad : AbstractDiagram | MCSB[ad] and HSB[ad] and TSB[ad] and DSB[ad]

	
}run W1 for 4 but exactly 1 AbstractDiagram

assert Phase3 {
	#Heat = 0 // Heat to change
	 and #Dry = 0 // Dry to change
           and #Delay = 0 // Delay to change
	implies P2
}check Phase3 for 4 but exactly 1 AbstractDiagram
