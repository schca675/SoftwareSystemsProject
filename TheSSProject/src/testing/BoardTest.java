package testing;

import model.Board;
import model.PlayerID;

public class BoardTest {
	
	public static final int LENGTH = 5;
	public static final int WIDTH = 7;
	public static final int HEIGHT = 6;
	public static final int WIN = 5;
	
	private Board<PlayerID> board;
	private Board<PlayerID> specialBoard;
	
	@Before
	public void setUp() {
		board = new Board<PlayerID>();
		specialBoard = new Board<PlayerID>(LENGTH, WIDTH, HEIGHT, WIN);
	}

	// <------ Test the constructors ------>
	
	@Test
	public void testDefaultDimension() {
		assertEquals(Board.DEFAULT_XDIM, board.getXDim());
		assertEquals(Board.DEFAULT_YDIM, board.getYDim());
		assertEquals(Board.DEFAULT_ZDIM, board.getZDim());
		assertEquals(Board.DEFAULT_WIN, board.getWinningLength());
	}

	@Test
	public void testSpecialDimension() {
		assertEquals(LENGTH, specialBoard.getXDim());
		assertEquals(WIDTH, specialBoard.getYDim());
		assertEquals(HEIGHT, specialBoard.getZDim());
		assertEquals(WIN, specialBoard.getWinningLength());
	}
	
	// <------ Test the queries ------>
	
	@Test 
	public void testCheckMove(){
		assertTrue(board.checkMove(1, 1));
		assertTrue(board.checkMove(4, 4));
		assertTrue(board.checkMove(2, 3));
		assertFalse(board.checkMove(-1, -1));
		assertFalse(board.checkMove(0, 0));
		assertFalse(board.checkMove(0, 3));
		assertFalse(board.checkMove(3, 0));
		assertFalse(board.checkMove(5, 5));
		assertFalse(board.checkMove(5, 2));
		assertFalse(board.checkMove(2, 5));		
	}
	
	@Test
	public void testCheckCellOwner() {
		assertNull(board.getCellOwner(1, 1, 1));
		board.makeMove(1, 1, PlayerID.O);
		assertEquals(board.getCellOwner(1, 1, 1), PlayerID.O);		
	}
	
	@Test
	public void testIsEmptyCell() {
		assertTrue(board.isEmptyCell(1, 1, 1));
		board.makeMove(1, 1, PlayerID.O);
		assertFalse(board.isEmptyCell(1, 1, 1));
	}
	
	@Test
	public void testisFull() {
		
	}
	
	@Test
	public void getTowerHeight() {
		assertEquals(0, board.getTowerHeight(1, 2));
		board.makeMove(1, 2, PlayerID.O);
		board.makeMove(1, 2, PlayerID.O);
		board.makeMove(1, 2, PlayerID.O);
		assertEquals(3, board.getTowerHeight(1, 2));
	}
	
	// Test X - dimension
	@Test 
	public void testHasWonXDir() {
		
	}
	
	// Test Y - dimension
	@Test 
	public void testHasWonYDir() {
		
	}
	
	// Test Z - direction
	@Test 
	public void testHasWonZDir() {
		
	}
	
	// Test X+Y-direction
	@Test 
	public void testHasWonXpYDir() {
		
	}
	
	// Test X-Y-direction
	@Test 
	public void testHasWonXmYDir() {
		
	}
	
	//Test X+Z-direction
	@Test 
	public void testHasWonXpZDir() {
		
	}
	
	//Test X-Z-direction
	@Test 
	public void testHasWonXmZDir() {
		
	}
	
	//Test Y+Z-direction
	@Test 
	public void testHasWonYpZDir() {
		
	}
	
	//Test Y-Z-direction
	@Test 
	public void testHasWonYmZDir() {
		
	}
	
	//test X+Y+Z-direction
	@Test 
	public void testHasWonXpYpZDir() {
		
	}
	
	//Test X+Y-Z-direction
	@Test 
	public void testHasWonXpYmZDir() {
		
	}
	
	//Test X-Y+Z-direction
	@Test 
	public void testHasWonXmYpZDir() {
		
	}
	
	//Test X-Y-Z-direction
	@Test 
	public void testHasWonXmYmZDir() {
		
	}
	
	@Test
	public void testisValidTowerDef() {
		assertTrue(board.isValidTower(1, 1));
		assertTrue(board.isValidTower(1, 3));
		assertTrue(board.isValidTower(2, 1));
		assertTrue(board.isValidTower(4, 4));
		assertTrue(board.isValidTower(4, 3));
		assertTrue(board.isValidTower(2, 4));
		assertFalse(board.isValidTower(0, 0));
		assertFalse(board.isValidTower(0, 1));
		assertFalse(board.isValidTower(3, 1));
		assertFalse(board.isValidTower(5, 2));
		assertFalse(board.isValidTower(4, 5));
		assertFalse(board.isValidTower(5, 5));		
	}
	
	@Test
	public void testisValidTowerSpec() {		
		assertTrue(specialBoard.isValidTower(5, 7));
		assertFalse(specialBoard.isValidTower(6, 5));
		assertFalse(specialBoard.isValidTower(3, 8));
	}
	
	@Test
	public void testisValidCell() {
		
	}

	// <------ Test the commands ------>
	
	@Test
	public void testMakeMove() {
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.X);
		assertEquals(board.getCellOwner(1, 1, 1), PlayerID.O);
		assertEquals(board.getCellOwner(1, 1, 2), PlayerID.O);
		assertNotEquals(board.getCellOwner(1, 1, 3), PlayerID.O);
		assertEquals(board.getCellOwner(1, 1, 3), PlayerID.X);
	}
	
	@Test
	public void testReset(){
		
	}
	
	
}
