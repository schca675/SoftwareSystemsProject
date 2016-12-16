package ss.week3.hotel;

import ss.week3.hotel.Bill.Item;

public class PricedRoom extends Room implements Item {
	private double price;

	//@ private invariant price >= 0;
	
	/**
	 * Creation of a priced safe.
	 * @param safePrice Price of the safe
	 * @param roomNumber number of the room
	 * @param roomPrice price of the room
	 */
	
	//@requires roomPrice >=0 && safePrice >=0 && roomNumber>=0;
	//@ensures getAmount() == roomPrice;
	public PricedRoom(int roomNumber, double roomPrice, double safePrice) {
		super(roomNumber, new PricedSafe(safePrice));
		price = roomPrice;
	}
	
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
	 * Returns the room with the price per night.
	 * @return room with price per night
	 */
	@Override
	/*@ pure */ public String toString() {
		return "Room " + super.getNumber() + " with a nightly price of " + 
				String.format("%.2f", price) + "€";
	}
}
