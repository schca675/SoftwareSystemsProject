package ss.week3.hotel;

import ss.week3.hotel.Bill.Item;

public class PricedSafe extends Safe implements Item {
	private double price;
	
	//@ private invariant price >= 0;
	
	// -------------- Constructor ----------
	
	/**
	 * Creation of a priced safe.
	 * @param safePrice Price of the safe
	 */
	//requires safePrice >=0;
	//@ensures getAmount() == safePrice;
	public PricedSafe(double safePrice) {
		super();
		price = safePrice;		
	}

    //--------------- Queries --------------
	
	
	/** 
	 * Returns the price of the safe.
	 * @return price of the safe
	 */
	
	//@ ensures \result >= 0;
	@Override
	/*@ pure */ public double getAmount() {
		return price;
	}
	
	/** 
	 * Returns the Safe with its price to activate.
	 * @return safe with price to activate.
	 */
	/*@ pure */ public String toString() {
		return "Safe with price " + price;
	}

}
