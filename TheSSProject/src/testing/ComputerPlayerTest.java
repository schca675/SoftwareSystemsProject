package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import model.Board;
import model.ComputerPlayer;
import model.RandomStrategy;
import model.SmartStrategy;
import model.Strategy;
import model.TowerCoordinates;

public class ComputerPlayerTest {

	public static final int TESTTIMES = 2;
	public static final int ID = 1;
	private Board board;
	private ComputerPlayer randi;
	private ComputerPlayer trams;
	private ComputerPlayer defaulty;
	private Strategy random;
	private Strategy smart;
	
	/**
	 * Create different instances of Computer Players.
	 */
	@Before
	public void setup() {
		random = new RandomStrategy();
		smart = new SmartStrategy();
		randi = new ComputerPlayer(random, ID);
		board = new Board();
		trams = new ComputerPlayer(smart, ID);
		defaulty = new ComputerPlayer(ID);
	}
	
	/**
	 * Test if the names of the ComputerPlayers 
	 * correspond to the names of the strategies.
	 */
	@Test
	public void testName() {
		assertEquals(random.getName(), randi.name);
		assertEquals(smart.getName(), trams.name);
		assertEquals(random.getName(), defaulty.name);
		
	}
	
	/**
	 * Test the ID's.
	 */
	@Test
	public void testID() {
		assertEquals(ID, randi.playerID);
		assertEquals(ID, trams.playerID);
		assertEquals(ID, defaulty.playerID);
	}
	
	/**
	 * Test the determine Move method of Randi.
	 */
	@Test
	public void testDetermineRandisMove() {
		TowerCoordinates coord = randi.determineMove(board);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
	
	/**
	 * Test the determine Move method of Trams.
	 */
	@Test
	public void testDetermineTramsMove() {
		TowerCoordinates coord = trams.determineMove(board);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
	
	/**
	 * Test the determine Move method of a default computer player.
	 */
	@Test
	public void testDetermineDefaultysMove() {
		TowerCoordinates coord = defaulty.determineMove(board);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
}
