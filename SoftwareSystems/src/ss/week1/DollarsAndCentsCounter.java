package ss.week1;

public class DollarsAndCentsCounter {
	public int dollars;
	public int cents;
	
	public DollarsAndCentsCounter() {
		dollars = 0;
		cents = 0;
	}
		
	public int dollars() {
		return dollars;
	}
	
	public int cents() {
		return cents;
	}
	
	public void add (int addDollars, int addCents) {
		if ((addDollars >= 0) && (addCents >= 0) && (addCents <=100)) {
		   dollars = dollars + addDollars;
		   cents = cents + addCents;
		   if (cents >= 100) {
		     	dollars = dollars +1;
			    cents = cents -100;
		    }
		}
	}
	
	public void reset() {
		dollars = 0;
		cents = 0;			
	}
	
		

}
