package testing;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import model.Player;

public class PlayerTest {

	public static final String NAME = "Test";
	public static final int ID = 1;
	private Player player;
	
	@Before
	public void setup() {
		player = new Player(NAME, ID);
	}
	
	@Test
	public void testName() {
		assertEquals(NAME, player.name);
	}
	
	@Test
	public void testID() {
		assertEquals(ID, player.playerID);
	}
}
