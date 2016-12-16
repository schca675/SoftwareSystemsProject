package ss.week3.hotel;

import ss.week3.hotel.Bill.Item;

public class TestBill implements Item {
	private double amount;
	private String text;

	public TestBill(double amount, String text) {
		this.amount = amount;
		this.text = text;
	}

	@Override
	public double getAmount() {
		return amount;
	}
	
	public String toString() {
		return text;
	}

}
