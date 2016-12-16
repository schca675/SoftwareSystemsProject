package ss.week3.test;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import ss.week3.hotel.Bill;
import ss.week3.hotel.TestBill;

public class BillTest {
	public Bill bill;
	TestBill objectA;
	TestBill objectB;
	TestBill objectC;
	int a;
	int b;
	int c;

	@Before
	public void setup() {
		a = 6;
		b = 3;
		c = 4;
		bill = new Bill(System.out);
		objectA = new TestBill(a, "Object A");
		objectB = new TestBill(b, "Object B");
		objectC = new TestBill(c, "Object C");

	}

	@Test
	public void testSetup() {
		assertEquals(0, bill.getSum(), 0.0001);
	}

	@Test
	public void addNewItem() {
		bill.newItem(objectA);
		assertEquals(a, bill.getSum(), 0.0001);
		bill.newItem(objectB);
		assertEquals(b + a, bill.getSum(), 0.0001);
		bill.newItem(objectC);
		assertEquals(a + b + c, bill.getSum(), 0.0001);
	}

	@Test
	public void testSum() {
		bill.newItem(objectA);
		assertEquals(a, bill.getSum(), 0.0001);
		bill.newItem(objectB);
		assertEquals(b + a, bill.getSum(), 0.0001);
		bill.newItem(objectC);
		assertEquals(a + b + c, bill.getSum(), 0.0001);
		bill.close();
	}
}
