package clientserver;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Vector;

/**
 * P2 prac wk5. <br>
 * Server. A Thread class that listens to a socket connection on a specified
 * port. For every socket connection with a Client, a new ClientHandler thread
 * is started.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Server extends Thread {
	
	//PROTOCOL
	public static final String ACCEPT_CONNECT = "OK";
	public static final String ERROR = "ERROR";
	public static final String LOBBY = "LOBBY";
	public static final String INVITE = "INVITE";
	public static final String GAME_START = "START";
	public static final String GAME_END = "END";
	public static final String REQUEST_MOVE = "REQUEST";
	public static final String MOVE_OK = "MOVE";
	public static final String BOARD = "BOARD";
	public static final String CHAT = "CHAT";
	public static final String LEADERBOARD = "LEADERBOARD";
	//END OF PROTOCOL
	private int port;
	private MessageUI mui;
	private Collection<ClientHandler> threads;

	/** Constructs a new Server object */
	public Server(int portArg, MessageUI muiArg) {
		this.port = portArg;
		this.mui = muiArg;
		this.threads = new LinkedList<ClientHandler>();
	}

	/**
	 * Listens to a port of this Server if there are any Clients that would like
	 * to connect. For every new socket connection a new ClientHandler thread is
	 * started that takes care of the further communication with the Client.
	 */
	public void run() {
		try {
			ServerSocket ss = new ServerSocket(port);
			while (true) {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				addHandler(ch);
				ch.announce();
				ch.start();
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients.
	 * 
	 * @param msg
	 *            message that is send
	 */
	public void broadcast(String msg) {
		if (msg != null) {
			for (ClientHandler ch : threads) {
				ch.sendMessage(msg);
			}
			mui.addMessage(msg);
		}
	}

	/**
	 * Add a ClientHandler to the collection of ClientHandlers.
	 * 
	 * @param handler
	 *            ClientHandler that will be added
	 */
	public void addHandler(ClientHandler handler) {
		threads.add(handler);
	}

	/**
	 * Remove a ClientHandler from the collection of ClientHanlders.
	 * 
	 * @param handler
	 *            ClientHandler that will be removed
	 */
	public void removeHandler(ClientHandler handler) {
		threads.remove(handler);
	}

} // end of class Server
