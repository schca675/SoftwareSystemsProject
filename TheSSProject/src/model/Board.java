package model;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

public class Board {
	
	// <------ Constants ------>
	
	public static final int DEFAULT_XDIM = 4;
	public static final int DEFAULT_YDIM = 4;
	public static final int DEFAULT_ZDIM = 4;
	public static final int DEFAULT_WIN = 4;
	public static final int UNLIMITED_Z = -1;
	
	// <------ INSTANCE VARIABLES ------>
	
	// With public final, they are visible but can't be changed after being set.
	// Saves the redundant getters.
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winningLength;
	private List<List<Integer>> boardData;
	
	
	// <------ CONSTRUCTORS ------>
	
	/** Create a new board with specified dimensions and winning length.
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	  @ 			|| (zDim > 0 && winningLength <= zDim) || (zDim == UNLIMITED_Z);
	 */
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	public Board(int xDim, int yDim, int zDim, int winningLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
		reset();
	}
	
	/** Create a board with default settings and rules.
	 * 
	 */
	public Board() {
		this(DEFAULT_XDIM, DEFAULT_YDIM, DEFAULT_ZDIM, DEFAULT_WIN);
	}
	
	
	// <------ QUERIES ------>	
	
	// <------ Used by external code ------>
	
	/** Checks whether a piece can be added at (<code>x</code>, <code>y</code>), i.e. if 
	 * (<code>x</code>, <code>y</code>) are	within the board dimensions (<code>xDim</code>, 
	 * <code>yDim</code>) and if the tower height is less than <code>zDim</code>.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (<code>x</code>, <code>y</code>) exists and isn't full
	 */
	//@ ensures zDim == UNLIMITED_Z ==> \result == (isValidTower(x,y));
	//@ ensures zDim > 0 ==> \result == (isValidTower(x,y) && getTowerHeight(x,y) < zDim);
	/*@ pure */ public boolean checkMove(int x, int y) throws CoordinatesOutOfBoundsException, 
																TowerIsAlreadyFullException {
		if (zDim == UNLIMITED_Z) {
			if (!isValidTower(x, y)) {
				throw new CoordinatesOutOfBoundsException(x, y, this);
			}
		} else {
			return isValidTower(x, y) && getTowerHeight(x, y) < zDim;
		}
	}
	
	/** Checks whether the <i>last added</i> piece at (<code>x</code>, <code>y</code>) belongs to a
	 * winning set, i.e. it belongs to a connected set of <code>winningLength</code> pieces 
	 * belonging to its owner.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return Piece at (<code>x</code>, <code>y</code>, <code>getTowerHeight(z)</code>) belongs to
	 * winning set
	 */
	//@ requires isValidCell(x,y,getTowerHeight(x,y)) && !isEmptyCell(x,y,getTowerHeight(x,y));
	//TODO: ensures part?
	/*@ pure */ public boolean hasWon(int x, int y) throws CoordinatesOutOfBoundsException {
		if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, this);
		}
		int z = getTowerHeight(x, y);
		Integer owner = getCellOwner(x, y, z);
		// Linearly independent direction vectors:
		// (1,0,0) X-direction
		// (0,1,0) Y-direction
		// (0,0,1) Z-direction
		// (1,1,0) X+Y-direction
		// (1,-1,0) X-Y-direction
		// (1,0,1) X+Z-direction
		// (1,0,-1) X-Z-direction
		// (0,1,1) Y+Z-direction
		// (0,1,-1) Y-Z-direction
		// (1,1,1) X+Y+Z-direction
		// (1,1,-1) X+Y-Z-direction
		// (1,-1,1) X-Y+Z-direction
		// (1,-1,-1) X-Y-Z-direction
		return directionHasWon(x, y, z, 1, 0, 0, owner) || 
				directionHasWon(x, y, z, 0, 1, 0, owner) || 
				directionHasWon(x, y, z, 0, 0, 1, owner) || 
				directionHasWon(x, y, z, 1, 1, 0, owner) ||
				directionHasWon(x, y, z, 1, -1, 0, owner) || 
				directionHasWon(x, y, z, 1, 0, 1, owner) ||
				directionHasWon(x, y, z, 1, 0, -1, owner) || 
				directionHasWon(x, y, z, 0, 1, 1, owner) ||
				directionHasWon(x, y, z, 0, 1, -1, owner) || 
				directionHasWon(x, y, z, 1, 1, 1, owner) ||
				directionHasWon(x, y, z, 1, 1, -1, owner) || 
				directionHasWon(x, y, z, 1, -1, 1, owner) ||
				directionHasWon(x, y, z, 1, -1, -1, owner);
	}
	
	/** Checks whether the board is full.
	 * 
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isValidCell(x,y,z); !isEmptyCell(x,y,z));
	/*@ pure */ public boolean isFull() {
		if (zDim == UNLIMITED_Z) {
			return false;
		} else {
			for (List<Integer> tower : boardData) {
				if (tower.size() < zDim) {
					return false;
				}
			}
			return true;
		}
	}
	
	/** Returns a <code>List</code> of <code>Coordinates</code> of each tower where a piece can be 
	 * added, i.e. towers with valid coordinates that are not full.
	 * 
	 * @return <code>List</code> of <code>Coordinates</code> of available towers
	 */
	/*@ ensures \forall TowerCoordinates coord; \result.contains(coord); 
	  @										checkMove(coord.getX(),coord.getY()); 
	/*@ pure */ public List<TowerCoordinates> getAvailableTowers() {
		ListIterator<List<Integer>> iterator = boardData.listIterator();
		List<TowerCoordinates> availableTowers = new ArrayList<TowerCoordinates>();
		if (zDim == UNLIMITED_Z) {
			while (iterator.hasNext()) {
				availableTowers.add(getTowerCoordinates(iterator.nextIndex()));
				iterator.next();
			}
		} else {
			while (iterator.hasNext()) {
				int x = getTowerCoordinates(iterator.nextIndex()).getX();
				int y = getTowerCoordinates(iterator.nextIndex()).getY();
				if (getTowerHeight(x, y) < zDim) {
					availableTowers.add(new TowerCoordinates(x, y));
				}
				iterator.next();
			}
		}
		return availableTowers;
	}
	
	/** Creates and returns a deep copy of the board.
	 * 
	 * @return Deep copy of this board
	 */
	//@ ensures \result.equals(this);
	/*@ pure */ public Board deepCopy() {
		Board boardCopy = new Board(xDim, yDim, zDim, winningLength);
		Iterator<List<Integer>> oldBoardIterator = boardData.iterator(); 
		Iterator<List<Integer>> newBoardIterator = boardCopy.boardData.iterator(); 
		while (oldBoardIterator.hasNext()) {
			newBoardIterator.next().addAll(oldBoardIterator.next());
		}
		return boardCopy;
	}
	
	/** Creates and returns a deep copy of the <code>boardData</code>, to use for the view.
	 * 
	 * @return Copy of the board data.
	 */
	/*@ pure */ public List<List<Integer>> deepDataCopy() {
		return deepCopy().boardData;
	}
	
	// Still needed for current implementation of the controller.
	/** Returns the height of the tower at (<code>x</code>, <code>y</code>).
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return The height of the tower at (<code>x</code>, <code>y</code>)
	 */
	//@ requires isValidTower(x,y);
	//@ ensures \result >= 0 && (\result <= zDim || zDim == UNLIMITED_Z);
	//@ ensures \forall int z; isValidCell(x,y,z); isEmptyCell(x,y,z) == (z > \result);
	/*@ pure */ public int getTowerHeight(int x, int y) throws CoordinatesOutOfBoundsException {
		if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, this);
		}
		return getTower(x, y).size();
	}
	
	// Used by test class only
	/** Returns the owner of the cell (<code>x</code>, <code>y</code>, <code>z</code>), null if no
	 *  owner.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner, null if no owner
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == null || \result instanceof Integer;
	/*@ pure nullable */ public Integer getCellOwner(int x, int y, int z) throws 
					CoordinatesOutOfBoundsException {
		if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, z, this);
		}
		if (z <= getTowerHeight(x, y)) {
			return getTower(x, y).get(z - 1);
		} else {
			return null;
		}
	}
	
	// Used by test class only
	/** Checks whether the given cell is empty, i.e. <code>getCellOwner(x, y, z) == null</code>.
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (<code>x</code>, <code>y</code>, <code>z</code>) is empty
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == (getCellOwner(x,y,z) == null);
	/*@ pure */ public boolean isEmptyCell(int x, int y, int z) throws 
					CoordinatesOutOfBoundsException {
		if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, z, this);
		}
		return getCellOwner(x, y, z) == null;
	}
	
	// <------ Not used by external code ------>
	
	/** Gets the tower at (<code>x</code>, <code>y</code>).
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (<code>x</code>, <code>y</code>)
	 */
	//@ requires isValidTower(x,y);
	/*@ pure */ private List<Integer> getTower(int x, int y) {
		return boardData.get((x - 1) + (y - 1) * yDim);
	}
	
	/** Checks whether the direction (<code>xDir</code>, <code>yDir</code>, 
	 * <code>zDir</code>), including its reverse, starting at the cell (<code>x</code>, 
	 * <code>y</code>, <code>z</code>) is winning. 
	 * 
	 * @param x X position of cell
	 * @param y Y position of cell
	 * @param z Z position of cell
	 * @param xDir X direction
	 * @param yDir Y direction
	 * @param zDir Z direction
	 * @return Direction has won
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	//TODO: ensures part?
	/*@ pure */ private boolean directionHasWon(int x, int y, int z, 
													int xDir, int yDir, int zDir, Integer owner) {
		int connectedPieces = 1;
		int distance = 1;
		int sign = 1;
		while (connectedPieces < winningLength) {
			int checkX = x + sign * distance * xDir;
			int checkY = y + sign * distance * yDir;
			int checkZ = z + sign * distance * zDir;
			if (isValidCell(checkX, checkY, checkZ) && getCellOwner(checkX, checkY, checkZ) != null
					&& getCellOwner(checkX, checkY, checkZ).equals(owner)) {
				connectedPieces = connectedPieces + 1;
				distance = distance + 1;
			} else {
				if (sign == 1) {
					//Reverse
					sign = -1;
					distance = 1;
				} else {
					//If reversed already, terminate
					return false;
				}
			}
		}
		return true;
	}
	
	/** Checks whether (<code>x</code>, <code>y</code>) is a valid tower on the board, i.e. whether
	 * the tower coordinates are within the dimensions.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return (<code>x</code>, <code>y</code>) are valid tower coordinates
	 */
	//@ ensures \result == (x > 0 && x <= xDim && y > 0 && y <= yDim);
	/*@ pure */ public boolean isValidTower(int x, int y) {
		return x > 0 && x <= xDim && y > 0 && y <= yDim;
	}
	
	/** Checks whether (<code>x</code>, <code>y</code>, <code>z</code>) is a valid cell on the 
	 * board, i.e. whether the cell coordinates are within the dimensions.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (<code>x</code>, <code>y</code>, <code>z</code>) are valid cell coordinates
	 */
	//@ ensures \result == (isValidTower(x,y) && ((z > 0 && z <= zDim) || zDim == UNLIMITED_Z));
	/*@ pure */ public boolean isValidCell(int x, int y, int z) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && z > 0 && z <= zDim;
		}
	}
	
	/** Returns the <code>Coordinates</code> belonging to a tower index.
	 * 
	 * @param i index
	 * @return <code>Coordinates</code> of tower
	 */
	//@ requires i >= 0 && i < xDim * yDim - 1;
	//@ ensures isValidTower(\result.getX(),\result.getY());
	/*@ pure */ private TowerCoordinates getTowerCoordinates(int i) {
		int x = i % yDim + 1;
		int y = i / yDim + 1;
		return new TowerCoordinates(x, y);
	}
	
	
	// <------ COMMANDS ------>
	
	// <------ Used by external code ------>
	
	/** Add a piece to the tower at (<code>x</code>, <code>y</code>).
	 * 
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @param playerID ID of player that makes a move
	 */
	//@ requires checkMove(x,y);
	/*@ ensures getCellOwner(x,y,getTowerHeight(x,y)) == playerID && 
	  @ 								getTowerHeight(x,y) == \old(getTowerHeight(x,y)) + 1;
	 */
	public void makeMove(int x, int y, Integer playerID) throws CoordinatesOutOfBoundsException, 
																TowerIsAlreadyFullException {
		if (checkMove(x, y)) {
			getTower(x, y).add(playerID);
		} else if (!isValidTower(x, y)) {
			throw new CoordinatesOutOfBoundsException(x, y, this);
		} else if (zDim != UNLIMITED_Z && !(getTowerHeight(x, y) < zDim)) {
			throw new TowerIsAlreadyFullException();
		}
	}
	
	// <------ Not used by external code ------>
	
	/** Resets the board to an empty board.
	 * 
	 */
	//@ ensures \forall int x,y,z; isValidCell(x,y,z); isEmptyCell(x,y,z);
	public void reset() {
		boardData = new ArrayList<List<Integer>>(xDim * yDim);
		if (zDim == UNLIMITED_Z) {
			for (int i = 0; i < xDim * yDim; i++) {
				boardData.add(new ArrayList<Integer>(50));
			}
		} else {
			for (int i = 0; i < xDim * yDim; i++) {
				boardData.add(new ArrayList<Integer>(zDim));
			}
		}
	}
}
