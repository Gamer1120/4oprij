package game;
/**
 * Strategy interface for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public interface Strategy {
	public String getName();

	public int determineMove(Board b, Disc d);
}
