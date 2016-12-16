package ss.week2.test;

import org.junit.Before;
import org.junit.Test;

import ss.week2.hotel.Safe;

import static org.junit.Assert.*;

public class SafeTest {
	private static final String WRONGPASSWORD = "cbfvfjbjf";
	private static final String RIGHTPASSWORD = "acdefghcudnfdj";
	private Safe safe;

	@Before
	public void setUp() throws Exception {
		safe = new Safe();
	}
	
	@Test
	public void testInitialization1() {
		assertFalse(safe.isActive());
		assertFalse(safe.isOpen());
		assertNotNull(safe.getPassword());		
	}
	
	@Test 
	public void testisActive() {
		assertFalse(safe.isActive());	
		safe.activate(RIGHTPASSWORD);
		assertTrue(safe.isActive());
	}
	
	@Test 
	public void testisOpen() {
		safe.activate(RIGHTPASSWORD);
		assertFalse(safe.isOpen());
		safe.open(RIGHTPASSWORD);
		assertTrue(safe.isOpen());
	}
	
	@Test
	public void testDeactivate() {
		safe.activate(RIGHTPASSWORD);
		safe.deactivate();
		assertFalse(safe.isActive());
		assertFalse(safe.isOpen());		
	}
	
	@Test 
	public void testgetPassword() {
		assertTrue(safe.getPassword().testWord(RIGHTPASSWORD));
	}
	
	@Test
	public void testClose() {
		safe.open(RIGHTPASSWORD);
		boolean activ = safe.isActive();
		safe.close();
		assertFalse(safe.isOpen());
		assertEquals(activ, safe.isActive());
	}
	
	@Test 
	public void testOpenDeactive() {
		// initial safe is deactivated
		safe.open(RIGHTPASSWORD);
		assertFalse(safe.isOpen());
		safe.open("bcxcfdjch");
		assertFalse(safe.isOpen());
	}
	
	@Test
	public void testOpenWrongPasswordActive() {
		safe.activate(RIGHTPASSWORD);
		safe.open(WRONGPASSWORD);
		assertFalse(safe.isOpen());		
	}
		
	@Test
	public void testOpenRightPasswordActive() {
		safe.activate(RIGHTPASSWORD);
		safe.open(RIGHTPASSWORD);
		assertTrue(safe.isOpen());
		
	}
     
	@Test
	public void testActivateRightPassword() {
		// initial safe is deactivated
		safe.activate(RIGHTPASSWORD);
		assertTrue(safe.isActive());
	}
	
	@Test
	public void testActivateWrongPassword() {
		// initial safe is deactivated
		safe.activate(WRONGPASSWORD);
		assertFalse(safe.isActive());
	}

	
	/* 
	 * Test plan:
	 * - Initialize safe
	 * 1) Test Initialization:
	 *  Is the safe deactivated and closed?
	 *  Does it have a password?
	 *  
	 *  2) Test methods, each time a new test case:
	 *    test method is Active 
	 *    test method is Open
	 * 	  test method deactivate;
	 *    test method getPassword
	 *    test method open with right and wrong password, deactivated
	 *    test method open with right password, activated
	 *    test method open with wrong password, activated
	 *    test method close
	 *    test method activate with right password
	 *    test method activate with wrong password.
	 */
}
